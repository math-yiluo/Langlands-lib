# Finite denominator multiplication of spherical Laurent series

This internal unit constructs the actual symmetric polynomial multiplier used
in the formal-series argument for the corrected essential-vector theorem. It
also proves the finite convolution, specialization and homogeneity properties
needed to multiply the Laurent series from `SphericalSeries`.

The construction accepts any scalar polynomial `P`; it does not assume that
`P` is a representation's L-factor polynomial. No conclusion about denominator
clearing, an upper degree bound, convergence, the functional equation, an
essential vector or a conductor is asserted here.

## Finite polynomial multipliers

For a commutative ring `A`, `finitePolynomialLaurentSeries P` is the finite sum

\[
  \sum_{m\in\operatorname{support}(P)} X^m P_m
\]

in the actual Mathlib Laurent-series ring `LaurentSeries A`. Here each term
is `HahnSeries.single (m : ℤ) (P.coeff m)`. Its coefficient at a natural
exponent `m` is exactly `P.coeff m`, and its coefficients at negative integer
exponents vanish.

`mul_finitePolynomialLaurentSeries_coeff` proves, for every Laurent series `S`
and integer `d`, the finite convolution formula

\[
 (S\cdot \operatorname{finitePolynomialLaurentSeries}(P))_d
   =\sum_{m\in\operatorname{support}(P)} S_{d-m}P_m.
\]

The proof distributes multiplication over the finite sum and applies the
Hahn-series single-term coefficient formula. Since every `m` is nonnegative,
if all `S_d` vanish below an integer `d₀`, the multiplied coefficients also
vanish below the same `d₀`. The construction and multiplication commute with
every commutative-ring homomorphism on coefficients; the proof compares the
natural and negative coefficient formulas and uses Hahn-series multiplicativity.

For the symmetric torus algebra over a field `K`, homogeneity of a product has
the sum of the two integer degrees. This follows from the multiplicativity of
simultaneous coordinate scaling and the integer-power addition identity for
the nonzero scaling unit.
`mul_finitePolynomialLaurentSeries_coeff_isHomogeneous` therefore proves that
the convolution coefficient at `d` is homogeneous of degree `d`, provided
`S_d` is homogeneous of degree `d` and `P_m` is homogeneous of degree `m`.
Each summand has degree `(d-m)+m=d`, and the homogeneous submodule is closed
under the finite sum.

These are algebraic hypotheses on arbitrary series and multipliers. For the
actual model series, coefficient homogeneity and a common lower bound have
already been proved in `SphericalSeries`.

## The actual coordinate product

For a finite variable type `σ` and a field `K`,
`coordinatePolynomialProduct σ K P` is the actual multivariate polynomial

\[
  Q(X_i)=\prod_{i\in σ}P(X_i).
\]

It is defined by evaluating `P` at each multivariate variable and taking the
finite product. Renaming variables by a permutation reindexes the product,
which proves symmetry. Homogeneous projection commutes with renaming, so each
degree component `Q_m` is symmetric too.

`symmetricPolynomialToTorus` is the algebra homomorphism from the symmetric
polynomial subalgebra to the existing symmetric Laurent subalgebra. Its
underlying map is the actual localization map on multivariate polynomials;
permutation invariance verifies membership in the target. Evaluation at a
tuple of units agrees with ordinary polynomial evaluation.

The standard scaling identity for a homogeneous multivariate polynomial is
proved monomial by monomial: scaling all variables by `c` gives the factor
`c^m` because every supported monomial has total degree `m`. When `K` is
infinite, evaluation separation in the Laurent algebra transfers this identity
to `IsSymmetricTorusHomogeneous`. This infinitude hypothesis is explicit in
the relevant theorems and holds for the intended coefficient field `ℂ`.

`coordinateDenominatorCoefficient σ K P m` is the localization image of the
actual symmetric homogeneous component `Q_m`. It vanishes when `m` exceeds
`Q.totalDegree`, and over an infinite field it is homogeneous of integer
degree `m`.

`coordinateDenominatorPolynomial σ K P` is the finite polynomial

\[
  D(X)=\sum_{m=0}^{\deg_{\mathrm{tot}}Q}X^m Q_m
\]

with coefficients in the symmetric Laurent algebra. The all-natural-degree
coefficient theorem identifies `D.coeff m` with the constructed component,
including degrees beyond the displayed finite range. Its coefficient at `m`
is homogeneous of degree `m` over an infinite coefficient field.

For every tuple of units `x` and scalar `t`, the proved evaluation formula is

\[
  D(t)(x)=\prod_{i\in σ}P(t x_i).
\]

The proof scales each homogeneous component, sums the homogeneous
decomposition of `Q`, and evaluates the original finite product. Finally,
over an infinite field, univariate polynomial evaluation separation gives the
exact polynomial specialization

\[
 D(X)(x)=\prod_{i\in σ}P(Xx_i).
\]

Thus this multiplier is built from the actual coordinate product, and its
identification with that product is proved.

## Provenance and remaining obligations

All definitions and deductions in this unit are internal algebraic
constructions using Mathlib's multivariate homogeneous components, polynomial
evaluation, the existing torus localization and Hahn-series operations.
Their intended application is the finite denominator multiplication and
homogeneous convolution passage of Hervé Jacquet, *A correction to Conducteur
des représentations du groupe linéaire* (2012), printed pages 520–521.
The implementation makes that formal algebra explicit and does not use the
flawed 1981 essential-vector existence argument.

Identifying an input `P` with an L-factor polynomial, proving the functional
equation, using it to obtain an upper degree bound, and proving the
essential-vector and conductor conclusions remain separate obligations.
