# Coordinate operations for plane curves

Author: Worker 2969.

This module develops internal algebraic tools for the elementary reduction
described in Wolfgang M. Schmidt, *Zur Methode von Stepanov*, Acta Arithmetica
24 (1973), printed p.349, registered source
`schmidt-1973-zur-methode-von-stepanov`. The source replaces a polynomial
`f(X,Y)=g(X^p,Y)` by `g`, preserving its rational zero count and absolute
irreducibility. These declarations are implementation tools for that
reduction, rather than separate transcriptions from the source.

`planeCurveExpandFirst` views the polynomial as a univariate polynomial in
its first variable, expands its exponents by a natural number, and transports
back. Its first partial degree is multiplied by that number; its second
partial degree is unchanged when the number is positive. The proofs compare
the supports of coefficients in the iterated polynomial representation.
Scalar extension and evaluation commute with this operation. The first
partial derivative corresponds to the derivative of the iterated polynomial.
If the expanded polynomial is absolutely irreducible, the original polynomial
is absolutely irreducible: transport to the iterated representation and use
the unit-reflecting expansion map.

When the first partial derivative vanishes in nonzero characteristic,
`planeCurve_exists_contractFirst` contracts the first exponents using
`Polynomial.expand_contract`. Over a finite field, the Frobenius automorphism
in the first coordinate induces an equivalence of the actual zero subtypes,
which proves equality of their `Nat.card` values. A positive first degree
strictly decreases under contraction, because a finite field has prime
characteristic at least two; the second degree stays fixed.

This helper module supplies the coordinate operations used by
`PlaneCurveSeparableModel`; the full elementary interface is assembled in
`PlaneCurveElementaryReductionsProof`.
