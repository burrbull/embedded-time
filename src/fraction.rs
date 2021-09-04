//! Fractional/Rational values
use crate::ConversionError;
use core::cmp::Ordering;
use core::ops;

/// A fractional value
///
/// Used primarily to define the _scaling factor_ for the [`Duration`], [`Rate`], [`Instant`] and
/// [`Clock`] traits and types.
///
/// [`Duration`]: duration/trait.Duration.html
/// [`Rate`]: rate/trait.Rate.html
/// [`Clock`]: clock/trait.Clock.html
/// [`Instant`]: instant/struct.Instant.html
#[derive(Copy, Clone, Debug)]
pub struct Fraction {
    /// Numerator.
    numer: u32,
    /// Denominator.
    denom: u32,
}

impl Fraction {
    /// Construct a new `Fraction`.
    ///
    /// A reduction is **not** performed. Also there is no check for a denominator of `0`. If these
    /// features are needed, use [`Fraction::new_reduce()`]
    pub const fn new(numerator: u32, denominator: u32) -> Self {
        Self {
            numer: numerator,
            denom: denominator,
        }
    }

    const fn try_reduce(mut self) -> Result<Self, ConversionError> {
        if self.denom == 0 {
            return Err(ConversionError::DivByZero);
        }
        if self.numer == 0 {
            self.denom = 1;
            return Ok(self);
        }
        if self.numer == self.denom {
            self.numer = 1;
            self.denom = 1;
            return Ok(self);
        }
        let g = gcd(self.numer, self.denom);

        self.numer = self.numer / g;
        self.denom = self.denom / g;
        Ok(self)
    }

    /// Return the numerator of the fraction
    pub const fn numerator(&self) -> &u32 {
        &self.numer
    }

    /// Return the denominator of the fraction
    pub const fn denominator(&self) -> &u32 {
        &self.denom
    }

    const fn const_eq(&self, other: &Self) -> bool {
        (self.numer as u64) * (other.denom as u64) == (self.denom as u64) * (other.numer as u64)
    }

    const fn const_cmp(&self, other: &Self) -> Ordering {
        let ad = (self.numer as u64) * (other.denom as u64);
        let bc = (self.denom as u64) * (other.numer as u64);
        if ad < bc {
            Ordering::Less
        } else if ad == bc {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

use core::hash::{Hash, Hasher};
impl Hash for Fraction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        recurse(self.numer, self.denom, state);

        fn recurse<H: Hasher>(numer: u32, denom: u32, state: &mut H) {
            if denom != 0 {
                let (int, rem) = ((numer / denom), (numer % denom));
                int.hash(state);
                recurse(denom, rem, state);
            } else {
                denom.hash(state);
            }
        }
    }
}

impl PartialEq for Fraction {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.const_eq(other)
    }
}

impl Eq for Fraction {}

impl PartialOrd for Fraction {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.const_cmp(other))
    }
}

impl Ord for Fraction {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.const_cmp(other)
    }
}

impl Fraction {
    /// Construct a new `Fraction`.
    ///
    /// A reduction and `denominator == 0` check **are** performed.
    ///
    /// # Errors
    ///
    /// [`ConversionError::DivByZero`] : A `0` denominator was detected
    pub const fn new_reduce(numerator: u32, denominator: u32) -> Result<Self, ConversionError> {
        Self::new(numerator, denominator).try_reduce()
    }

    /// Returns the value truncated to an integer
    pub const fn to_integer(&self) -> u32 {
        self.numer / self.denom
    }

    /// Constructs a `Fraction` from an integer.
    ///
    /// Equivalent to `Fraction::new(value,1)`.
    pub const fn from_integer(value: u32) -> Self {
        Self::new(value, 1)
    }

    /// Returns the reciprocal of the fraction
    pub const fn try_recip(self) -> Result<Self, ConversionError> {
        if self.numer == 0 {
            return Err(ConversionError::DivByZero);
        } else {
            Ok(Self::new(self.denom, self.numer))
        }
    }

    /// Checked `Fraction` × `Fraction` = `Fraction`
    ///
    /// Returns [`None`] for any errors
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use embedded_time::{fraction::Fraction, ConversionError};
    /// #
    /// assert_eq!(Fraction::new(1000, 1).checked_mul(&Fraction::new(5,5)),
    ///     Some(Fraction::new(5_000, 5)));
    ///
    /// assert_eq!(Fraction::new(u32::MAX, 1).checked_mul(&Fraction::new(2,1)),
    ///     None);
    /// ```
    pub const fn checked_mul(&self, rhs: &Self) -> Option<Self> {
        let gcd_ad = gcd(self.numer, rhs.denom);
        let gcd_bc = gcd(self.denom, rhs.numer);
        let numer = (self.numer / gcd_ad).checked_mul(rhs.numer / gcd_bc);
        let denom = (self.denom / gcd_bc).checked_mul(rhs.denom / gcd_ad);
        if let (Some(numer), Some(denom)) = (numer, denom) {
            if let Ok(f) = Self::new_reduce(numer, denom) {
                Some(f)
            } else {
                None
            }
        } else {
            None
        }
    }

    const fn is_zero(&self) -> bool {
        self.numer == 0
    }

    const fn zero() -> Self {
        Self::new(0, 1)
    }

    const fn one() -> Self {
        Self::new(1, 1)
    }

    /// Checked `Fraction` / `Fraction` = `Fraction`
    ///
    /// Returns [`None`] for any errors
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use embedded_time::{fraction::Fraction, ConversionError};
    /// #
    /// assert_eq!(Fraction::new(1000, 1).checked_div(&Fraction::new(10, 1000)),
    ///     Some(Fraction::new(1_000_000, 10)));
    ///
    /// assert_eq!(Fraction::new(1, u32::MAX).checked_div(&Fraction::new(2,1)),
    ///     None);
    /// ```
    pub const fn checked_div(&self, rhs: &Self) -> Option<Self> {
        if rhs.is_zero() {
            return None;
        }
        let (numer, denom) = if self.denom == rhs.denom {
            (self.numer, rhs.numer)
        } else if self.numer == rhs.numer {
            (rhs.denom, self.denom)
        } else {
            let gcd_ac = gcd(self.numer, rhs.numer);
            let gcd_bd = gcd(self.denom, rhs.denom);
            let numer = (self.numer / gcd_ac).checked_mul(rhs.denom / gcd_bd);
            let denom = (self.denom / gcd_bd).checked_mul(rhs.numer / gcd_ac);
            if let (Some(numer), Some(denom)) = (numer, denom) {
                (numer, denom)
            } else {
                return None;
            }
        };
        // Manual `reduce()`, avoiding sharp edges
        if denom == 0 {
            None
        } else if numer == 0 {
            Some(Self::zero())
        } else if numer == denom {
            Some(Self::one())
        } else {
            let g = gcd(numer, denom);
            let numer = numer / g;
            let denom = denom / g;
            Some(Self::new(numer, denom))
        }
    }
}

impl ops::Mul<Fraction> for u32 {
    type Output = Self;

    /// Panicky u32 × `Fraction` = u32
    fn mul(self, rhs: Fraction) -> Self::Output {
        (rhs * self).to_integer()
    }
}

impl ops::Div<Fraction> for u32 {
    type Output = Self;

    /// Panicky u32 / `Fraction` = u32
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Fraction) -> Self::Output {
        (rhs.try_recip()
            .unwrap_or_else(|_| panic!("division by zero"))
            * self)
            .to_integer()
    }
}

impl ops::Mul<Fraction> for u64 {
    type Output = Self;

    /// Panicky u64 × `Fraction` = u64
    fn mul(self, rhs: Fraction) -> Self::Output {
        let numer = rhs.numer as u64;
        let denom = rhs.denom as u64;
        let gcd = gcd_u64(denom, self);
        (numer * (self / gcd)) / (denom / gcd)
    }
}

impl ops::Div<Fraction> for u64 {
    type Output = Self;

    /// Panicky u64 / `Fraction` = u64
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Fraction) -> Self::Output {
        let numer = rhs.denom as u64;
        let denom = rhs.numer as u64;
        let gcd = gcd_u64(denom, self);
        (numer * (self / gcd)) / (denom / gcd)
    }
}

impl ops::Mul for Fraction {
    type Output = Self;

    /// Panicky `Fraction` × `Fraction` = `Fraction`
    ///
    /// # Panics
    ///
    /// The same reason the integer operation would panic. Namely, if the
    /// result overflows the type.
    fn mul(self, rhs: Self) -> Self::Output {
        let gcd_ad = gcd(self.numer, rhs.denom);
        let gcd_bc = gcd(self.denom, rhs.numer);
        Self::new_reduce(
            self.numer / gcd_ad * (rhs.numer / gcd_bc),
            self.denom / gcd_bc * (rhs.denom / gcd_ad),
        )
        .unwrap_or_else(|_| panic!("division by zero"))
    }
}

impl ops::Mul<u32> for Fraction {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: u32) -> Self {
        let gcd = gcd(self.denom, rhs);
        Self::new_reduce(self.numer * (rhs / gcd), self.denom / gcd)
            .unwrap_or_else(|_| panic!("division by zero"))
    }
}

impl ops::Div for Fraction {
    type Output = Self;

    /// Panicky `Fraction` / `Fraction` = `Fraction`
    ///
    /// # Panics
    ///
    /// The same reason the integer operation would panic. Namely, if the
    /// result overflows the type.
    fn div(self, rhs: Self) -> Self::Output {
        let gcd_ac = gcd(self.numer, rhs.numer);
        let gcd_bd = gcd(self.denom, rhs.denom);
        Self::new_reduce(
            self.numer / gcd_ac * (rhs.denom / gcd_bd),
            self.denom / gcd_bd * (rhs.numer / gcd_ac),
        )
        .unwrap_or_else(|_| panic!("division by zero"))
    }
}

impl Default for Fraction {
    fn default() -> Self {
        Self::new(1, 1)
    }
}

const fn gcd(mut m: u32, mut n: u32) -> u32 {
    // Use Stein's algorithm
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2
    let shift = (m | n).trailing_zeros();

    // divide n and m by 2 until odd
    m >>= m.trailing_zeros();
    n >>= n.trailing_zeros();

    while m != n {
        if m > n {
            m -= n;
            m >>= m.trailing_zeros();
        } else {
            n -= m;
            n >>= n.trailing_zeros();
        }
    }
    m << shift
}

const fn gcd_u64(mut m: u64, mut n: u64) -> u64 {
    // Use Stein's algorithm
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2
    let shift = (m | n).trailing_zeros();

    // divide n and m by 2 until odd
    m >>= m.trailing_zeros();
    n >>= n.trailing_zeros();

    while m != n {
        if m > n {
            m -= n;
            m >>= m.trailing_zeros();
        } else {
            n -= m;
            n >>= n.trailing_zeros();
        }
    }
    m << shift
}

#[cfg(test)]
mod tests {}
