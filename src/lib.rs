#![deny(missing_docs)]

//! # Closure Calculus
//! An implementation of Closure Calculus
//!
//! Based on paper by Barry Jay: https://dl.acm.org/doi/pdf/10.1145/3294032.3294085

use Expr::*;

/// Stores expressions for Closure Calculus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// Zero.
    J,
    /// Successor.
    R(Box<Expr>),
    /// Application freeze.
    F(Box<Expr>, Box<Expr>),
    /// Lambda with environment and body.
    L(Box<Expr>, Box<Expr>),
    /// Identity.
    I,
    /// Pair.
    P(Box<Expr>, Box<Expr>),
    /// Application.
    A(Box<Expr>, Box<Expr>),
}

impl Expr {
    /// Reduces expression.
    ///
    /// Returns `Ok(_)` if the expression was reduced.
    /// Returns `Err(_)` if the expression was not reduced.
    pub fn reduce(self) -> Result<Expr, Expr> {
        use Expr::*;

        match &self {
            A(a, b) => {
                match **a {
                    // J(t) => J'(t)
                    // R(t)(u) => R(t)'(u)
                    // r'(t)(u) => r'(t)'(u)
                    J | R(_) | F(_, _) => Ok(F(a.clone(), b.clone())),
                    // (\(J) ~ s = t)(u) => (u, s)(t)
                    L(ref s, ref t) => Ok(A(P(b.clone(), s.clone()).into(), t.clone())),
                    // I(t) => t
                    I => Ok((**b).clone()),
                    P(ref u, ref s) => {
                        match **b {
                            // (u, s)(J) => u
                            J => Ok((**u).clone()),
                            // (u, s)(R(t)) => s(t)
                            R(ref t) => Ok(A(s.clone(), t.clone())),
                            // (u, s)(r’(t)) => (u, s)(r)((u, s)(t))
                            F(ref r, ref t) =>
                                Ok(A(A(a.clone(), r.clone()).into(),
                                     A(a.clone(), t.clone()).into())),
                            // (u, s)(\(J) ~ r = t) => \(J) ~ (u, s)(r) = t
                            L(ref r, ref t) => Ok(L(A(a.clone(), r.clone()).into(), t.clone())),
                            // (u, s)(I) => I
                            I => Ok(I),
                            // (u, s)((r, t)) => ((u, s)(r), (u, s)(t))
                            P(ref r, ref t) =>
                                Ok(P(A(a.clone(), r.clone()).into(),
                                     A(a.clone(), t.clone()).into())),
                            A(_, _) => {
                                match (**b).clone().reduce() {
                                    Ok(x) => Ok(A(a.clone(), x.into())),
                                    Err(_) => Err(self),
                                }
                            }
                        }
                    }
                    A(_, _) => {
                        match (**a).clone().reduce() {
                            Ok(x) => Ok(A(x.into(), b.clone())),
                            Err(_) => Err(self),
                        }
                    }
                }
            }
            R(a) => {
                match (**a).clone().reduce() {
                    Ok(x) => Ok(R(x.into())),
                    Err(_) => Err(self),
                }
            }
            J | I => Err(self),
            F(a, b) => {
                let a = a.clone().reduce();
                let b = b.clone().reduce();
                match (a, b) {
                    (Err(_), Err(_)) => Err(self),
                    (Ok(a), Ok(b)) |
                    (Ok(a), Err(b)) |
                    (Err(a), Ok(b)) => Ok(F(a.into(), b.into())),
                }
            }
            L(a, b) => {
                let a = a.clone().reduce();
                let b = b.clone().reduce();
                match (a, b) {
                    (Err(_), Err(_)) => Err(self),
                    (Ok(a), Ok(b)) |
                    (Ok(a), Err(b)) |
                    (Err(a), Ok(b)) => Ok(L(a.into(), b.into())),
                }
            }
            P(a, b) => {
                let a = a.clone().reduce();
                let b = b.clone().reduce();
                match (a, b) {
                    (Err(_), Err(_)) => Err(self),
                    (Ok(a), Ok(b)) |
                    (Ok(a), Err(b)) |
                    (Err(a), Ok(b)) => Ok(P(a.into(), b.into())),
                }
            }
        }
    }

    /// Reduce until no further reductions can be done.
    pub fn reduce_all(self) -> Expr {
        let mut x = self;
        loop {
            match x.reduce() {
                Ok(y) => x = y,
                Err(x) => return x,
            }
        }
    }
}

impl Into<Expr> for usize {
    fn into(self) -> Expr {
        match self {
            0 => J,
            x => R(Box::new((x-1).into())),
        }
    }
}

/// The identity function.
///
/// `\(J) ~ I = J`
pub fn id() -> Expr {L(I.into(), J.into())}

/// The second argument function.
///
/// `\(J) ~ I = \(J) ~ I = J`
pub fn snd() -> Expr {L(I.into(), id().into())}

/// The first argument function.
///
/// `\(J) ~ I = \(J) ~ (J, I) = R(J)`
pub fn fst() -> Expr {
    L(
        I.into(),
        L(
            P(J.into(), I.into()).into(),
            R(J.into()).into(),
        ).into()
    )
}

/// Applies function to two arguments.
pub fn app2(a: Expr, b: Expr, c: Expr) -> Expr {A(A(a.into(), b.into()).into(), c.into())}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let a = A(J.into(), I.into());
        assert_eq!(a.reduce().unwrap(), F(J.into(), I.into()));
    }

    // id(x) = x
    #[test]
    fn test_id() {
        // (\(J) ~ I = J)(x)
        let x = J;
        let a = A(id().into(), x.clone().into());
        let a = a.reduce().unwrap();
        // (x, I)(J)
        assert_eq!(a, A(P(x.clone().into(), I.into()).into(), J.into()));
        let a = a.reduce().unwrap();
        assert_eq!(a, x);
    }

    // snd(x, y) = y
    #[test]
    fn test_snd() {
        // (\(J) ~ I = \(J) ~ I = J)(x)(y)
        let x: Expr = 2.into();
        let y: Expr = 3.into();
        let a = app2(snd(), x.clone(), y.clone());
        // (x, I)(\(J) ~ I = J)(y)
        let a = a.reduce().unwrap();
        assert_eq!(a, app2(P(x.clone().into(), I.into()), id(), y.clone()));
        // (\(J) ~ (x, I)(I) = J)(y)
        let a = a.reduce().unwrap();
        assert_eq!(a, A(
            L(A(P(x.clone().into(), I.into()).into(), I.into()).into(), J.into()).into(),
            y.clone().into()
        ));
        // (y, (x, I)(I))(J)
        let a = a.reduce().unwrap();
        assert_eq!(a, A(P(y.clone().into(), A(P(x.clone().into(), I.into()).into(), I.into()).into()).into(), J.into()));
        let a = a.reduce().unwrap();
        assert_eq!(a, y);
    }

    // fst(x, y) = x
    #[test]
    fn test_fst() {
        let x: Expr = 2.into();
        let y: Expr = 3.into();
        let a = app2(fst(), x.clone(), y.clone());
        assert_eq!(a.reduce_all(), x);
    }
}
