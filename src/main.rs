/// Mod integer algorithms

// Mod Int
// ------------------------------------------------------------------------------------
mod mod_int {
    use std::ops::*;
    pub trait Mod: Copy {
        fn m() -> i64;
    }
    #[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub struct ModInt<M> {
        pub x: i64,
        phantom: ::std::marker::PhantomData<M>,
    }
    impl<M: Mod> ModInt<M> {
        // x >= 0
        pub fn new(x: i64) -> Self {
            ModInt::new_internal(x % M::m())
        }
        fn new_internal(x: i64) -> Self {
            ModInt {
                x: x,
                phantom: ::std::marker::PhantomData,
            }
        }
        pub fn pow(self, mut e: i64) -> Self {
            debug_assert!(e >= 0);
            let mut sum = ModInt::new_internal(1);
            let mut cur = self;
            while e > 0 {
                if e % 2 != 0 {
                    sum *= cur;
                }
                cur *= cur;
                e /= 2;
            }
            sum
        }
        #[allow(dead_code)]
        pub fn inv(self) -> Self {
            self.pow(M::m() - 2)
        }
    }
    impl<M: Mod, T: Into<ModInt<M>>> Add<T> for ModInt<M> {
        type Output = Self;
        fn add(self, other: T) -> Self {
            let other = other.into();
            let mut sum = self.x + other.x;
            if sum >= M::m() {
                sum -= M::m();
            }
            ModInt::new_internal(sum)
        }
    }
    impl<M: Mod, T: Into<ModInt<M>>> Sub<T> for ModInt<M> {
        type Output = Self;
        fn sub(self, other: T) -> Self {
            let other = other.into();
            let mut sum = self.x - other.x;
            if sum < 0 {
                sum += M::m();
            }
            ModInt::new_internal(sum)
        }
    }
    impl<M: Mod, T: Into<ModInt<M>>> Mul<T> for ModInt<M> {
        type Output = Self;
        fn mul(self, other: T) -> Self {
            ModInt::new(self.x * other.into().x % M::m())
        }
    }
    impl<M: Mod, T: Into<ModInt<M>>> AddAssign<T> for ModInt<M> {
        fn add_assign(&mut self, other: T) {
            *self = *self + other;
        }
    }
    impl<M: Mod, T: Into<ModInt<M>>> SubAssign<T> for ModInt<M> {
        fn sub_assign(&mut self, other: T) {
            *self = *self - other;
        }
    }
    impl<M: Mod, T: Into<ModInt<M>>> MulAssign<T> for ModInt<M> {
        fn mul_assign(&mut self, other: T) {
            *self = *self * other;
        }
    }
    impl<M: Mod> Neg for ModInt<M> {
        type Output = Self;
        fn neg(self) -> Self {
            ModInt::new(0) - self
        }
    }
    impl<M> ::std::fmt::Display for ModInt<M> {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            self.x.fmt(f)
        }
    }
    impl<M: Mod> From<i64> for ModInt<M> {
        fn from(x: i64) -> Self {
            Self::new(x)
        }
    }
}

// FFT (in-place, verified as NTT only)
// R: Ring + Copy
// ------------------------------------------------------------------------------------
mod fft {
    use std::ops::*;
    // n should be a power of 2. zeta is a primitive n-th root of unity.
    // one is unity
    // Note that the result is bit-reversed.
    pub fn fft<R>(f: &mut [R], zeta: R, one: R)
    where
        R: Copy + Add<Output = R> + Sub<Output = R> + Mul<Output = R>,
    {
        let n = f.len();
        assert!(n.is_power_of_two());
        let mut m = n;
        let mut base = zeta;
        unsafe {
            while m > 2 {
                m >>= 1;
                let mut r = 0;
                while r < n {
                    let mut w = one;
                    for s in r..r + m {
                        let &u = f.get_unchecked(s);
                        let d = *f.get_unchecked(s + m);
                        *f.get_unchecked_mut(s) = u + d;
                        *f.get_unchecked_mut(s + m) = w * (u - d);
                        w = w * base;
                    }
                    r += 2 * m;
                }
                base = base * base;
            }
            if m > 1 {
                // m = 1
                let mut r = 0;
                while r < n {
                    let &u = f.get_unchecked(r);
                    let d = *f.get_unchecked(r + 1);
                    *f.get_unchecked_mut(r) = u + d;
                    *f.get_unchecked_mut(r + 1) = u - d;
                    r += 2;
                }
            }
        }
    }
    pub fn inv_fft<R>(f: &mut [R], zeta_inv: R, one: R)
    where
        R: Copy + Add<Output = R> + Sub<Output = R> + Mul<Output = R>,
    {
        let n = f.len();
        assert!(n.is_power_of_two());
        let zeta = zeta_inv; // inverse FFT
        let mut zetapow = Vec::with_capacity(20);
        {
            let mut m = 1;
            let mut cur = zeta;
            while m < n {
                zetapow.push(cur);
                cur = cur * cur;
                m *= 2;
            }
        }
        let mut m = 1;
        unsafe {
            if m < n {
                zetapow.pop();
                let mut r = 0;
                while r < n {
                    let &u = f.get_unchecked(r);
                    let d = *f.get_unchecked(r + 1);
                    *f.get_unchecked_mut(r) = u + d;
                    *f.get_unchecked_mut(r + 1) = u - d;
                    r += 2;
                }
                m = 2;
            }
            while m < n {
                let base = zetapow.pop().unwrap();
                let mut r = 0;
                while r < n {
                    let mut w = one;
                    for s in r..r + m {
                        let &u = f.get_unchecked(s);
                        let d = *f.get_unchecked(s + m) * w;
                        *f.get_unchecked_mut(s) = u + d;
                        *f.get_unchecked_mut(s + m) = u - d;
                        w = w * base;
                    }
                    r += 2 * m;
                }
                m *= 2;
            }
        }
    }
}

// Define Mod
// ------------------------------------------------------------------------------------
macro_rules! define_mod {
    ($struct_name: ident, $modulo: expr) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
        struct $struct_name {}
        impl mod_int::Mod for $struct_name {
            fn m() -> i64 {
                $modulo
            }
        }
    };
}

const MOD: i64 = 998_244_353;
define_mod!(P, MOD);
type MInt = mod_int::ModInt<P>;

// Polynomial shift
// ------------------------------------------------------------------------------------
fn fact_init(w: usize) -> (Vec<MInt>, Vec<MInt>) {
    let mut fac = vec![MInt::new(1); w];
    let mut invfac = vec![0.into(); w];
    for i in 1..w {
        fac[i] = fac[i - 1] * i as i64;
    }
    invfac[w - 1] = fac[w - 1].inv();
    for i in (0..w - 1).rev() {
        invfac[i] = invfac[i + 1] * (i as i64 + 1);
    }
    (fac, invfac)
}

fn taylor_shift_convolve<R>(a: &mut [MInt], c : MInt) {
    let n = a.len();

    let mut p = 1;
    while p < 2 * n {
        p *= 2;
    }
    let (fac, invfac) = fact_init(p);
    println!("fac {:?}", fac);
    println!("invfac {:?}", invfac);
    let mut f = vec![MInt::new(0); p];
    let mut g = vec![MInt::new(0); p];
    let mut cur = MInt::new(1);
    for i in 0..n {
        f[i] = fac[i] * a[i];
        g[(p - i) % p] = cur * invfac[i];
        cur *= c;
    }
    for i in f.iter() {
        println!("f[] {:?}", i);
    }
    for i in g.iter() {
        println!("g[] {:?}", i);
    }
    let zeta = MInt::new(3).pow((MOD - 1) / p as i64);
    println!("zeta = {}", zeta);
    let factor = MInt::new(p as i64).inv();
    fft::fft(&mut f, zeta, 1.into());
    fft::fft(&mut g, zeta, 1.into());
    for i in 0..p {
        f[i] *= g[i] * factor;
    }
    fft::inv_fft(&mut f, zeta.inv(), 1.into());
    println!("post convolvef {:?}", g);
    for i in 0..n {
        f[i] *= invfac[i];
    }
    // putvec!(f[..n]);
    println!("{:?}", f);


}

// Tags: polynomial-taylor-shift
fn main() {
    let a = [1, 2, 3, 4];
    let c = MInt::new(2);
    let mut a = a.into_iter().map(MInt::new).collect::<Vec<_>>();

    taylor_shift_convolve::<MInt>(&mut a, c);
}



#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_taylor_shift_shaw_traub_basic_prop() {
        // check f(x+c)(x+d) = f(x+c+d)
        let c = MInt::new(2);
        let d = MInt::new(3);
        let a = [1, 2, 3, 4, 0, 0, 0, 1];
        let a = a.into_iter().map(MInt::new).collect::<Vec<_>>();


        let mut fx_c = a.clone();
        taylor_shift_convolve::<MInt>(&mut fx_c, c);

        let mut fx_c_d = fx_c.clone();
        taylor_shift_convolve::<MInt>(&mut fx_c_d, d);

        let cd = c + d;
        let mut fx_cd = a.clone();
        taylor_shift_convolve::<MInt>(&mut fx_cd, cd);
        assert_eq!(fx_c_d, fx_cd);
    }
}
