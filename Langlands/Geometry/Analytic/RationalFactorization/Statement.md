# Spectrum-image factorization for rational quotients

Author: Worker 36.

`Langlands.Analytic.RationalFactorization.FactorizationStatement` quantifies
over a complete ultrametric normed field `K`, a presented strict affinoid
algebra `P`, a denominator `g`, and a finite numerator tuple `f`. The
denominator and numerators must generate the unit ideal in `P`.

For every presented strict affinoid algebra `Q` over the same `K` and
every bounded algebra map `φ : P → Q`, the target asserts an equivalence:

- Every point of the actual bounded multiplicative seminorm spectrum of
  `Q` pulls back into the rational locus `x(f_i) ≤ x(g)` in the spectrum
  of `P`.
- There is a unique bounded algebra map from the constructed rational
  quotient of `P` to `Q` whose composite with the structural map is `φ`.

The conclusion concerns the existing closed-ideal quotient of an enlarged
finite Tate algebra, its actual bounded structural map, and equality of
bounded algebra maps. No inverse of `φ(g)`, fraction tuple, monomial bound,
or factorization is supplied as input. Empty tuples, zero algebras,
nilpotents and trivial scalar valuations remain allowed. Both presented
algebras have carriers in the coefficient universe; their presentation
arities and ideals are independent.

This is a derived strict-test specialization of the factorization
property in Berkovich, *Non-Archimedean analytic spaces* (Trieste 2009),
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF page 9. Definition
2.1.11 on page 8 explains the reversal from space maps to bounded algebra
maps. The proof route is to deduce nonvanishing of `φ(g)` at every spectrum
point from the unit ideal and image containment, obtain an actual unit
using the strict-affinoid spectrum criterion, and form its actual
fractions. Their pointwise values are at most one. The strict-affinoid
spectral power-bound theorem then supplies the bounded monomials needed
by the existing quotient extension construction. Uniqueness is the
existing algebraic uniqueness over the base. Conversely, any
factorization pulls spectrum points back through the quotient, whose
image is in the rational locus.

The declaration defines an unproved proposition. It adds the
image-containment criterion to the earlier bounded-solution target.
The source tests against all affinoid spaces, including nonstrict
ones, whereas this target tests only the constructed presented strict
affinoids. Consequently it does not yet establish Definition 2.2.1 in
its full scope, even though the rational quotient is itself strict.
Arbitrary radii, comparison with the source's relative-series quotient,
and replacement of the algebraic unit-ideal hypothesis by absence of
common spectrum zeros are separate obligations. A structure sheaf or
glued analytic space is not asserted here.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Original author source: <https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf>.
