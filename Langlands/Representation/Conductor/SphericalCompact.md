# Compact support of the actual Laurent degree integrands

This internal prerequisite works over every nonarchimedean local field `F`,
with independent universes for `F` and the complex representation space.
It uses the actual smooth representation of `GL_(n+2)(F)`, an actual
Whittaker functional, and a vector in its coefficient model. The additive
character has integer conductor. Irreducibility, admissibility and
finite-dimensionality are not hypotheses.

The conclusions concern the previously defined Laurent corank-one integrand
and its restrictions to the actual Iwasawa degrees on
`N_(n+1)(F) \ GL_(n+1)(F)`. They establish compact support, vanishing in
sufficiently low degrees, and scalar coefficient integrability for the
Jacquet-normalized measure. They do not assert convergence of the sum over
all degrees, rational continuation, an essential identity, a factor
comparison, or any part of the essential-conductor theorem.

## Last exponent and spherical support

`uniformizer_zpow_mem_integer_iff` proves that the image of the unit
`ϖ^m` belongs to the valuation ring exactly when `m ≥ 0`. The proof uses
multiplicativity of the canonical valuation and the fact that the valuation
of a uniformizer lies strictly between zero and one.

`model_corankOne_last_exponent_lower_bound` supplies an integer `b`,
depending on the model vector, such that

`w(diag(torus(λ) k, 1)) ≠ 0` implies `λ_n ≥ b`

for every integer tuple `λ` and every integral invertible matrix `k`.
The proof applies the published smooth root bound to the ambient diagonal
`diag(ϖ^λ_0, …, ϖ^λ_n, 1)` and the integral matrix `diag(k,1)`.
At the last adjacent root, the ratio of diagonal entries is `ϖ^λ_n`.
If the smooth root bound has exponent `m`, it gives integrality of
`ϖ^(λ_n+m)`. The preceding valuation lemma gives `λ_n ≥ -m`.
The private matrix identity for `rankInclusion` verifies this diagonal
description entry by entry, including its last coordinate.

`model_corankOne_polynomial_exponents_lower_bound` then gives one integer
`b` for which every exponent of any nonzero value of
`corankOnePolynomialFunction` is at least `b`. Nonvanishing of the actual
spherical Laurent factor forces the Iwasawa tuple to be antitone. Remove
the upper-unipotent factor with the existing invariance theorem for the
whole Laurent function. Nonvanishing of the remaining function forces
nonvanishing of its model coefficient. The preceding last-coordinate
bound applies, and antitonicity bounds every other coordinate below by the
last one. No nonvanishing assertion about the Schur polynomial is needed.

## Finite tuples and compact carrier

`boundedDegreeExponents m b d` is the set of all integer tuples indexed
by `Fin m` whose entries are at least `b` and whose sum is `d`.
For `m = n+1`, `boundedDegreeExponents_finite` proves finiteness by
placing each coordinate in the finite integer interval

`[b, d - n*b]`.

Indeed, the other `n` coordinates sum to at least `n*b`; the fixed total
then gives the displayed upper bound. The finite product of these
intervals contains the set. `boundedDegreeExponents_eq_empty_of_lt`
also proves emptiness for `d < m*b`, by summing the lower bounds.

`boundedDegreeQuotientCarrier ϖ b d` is the union, over those bounded
tuples of length `n+1`, of the images of

`k ↦ [torus(λ) k]`

from the actual integral subgroup to the left-unipotent quotient.
`boundedDegreeQuotientCarrier_isCompact` proves compactness: the
level-zero integral group is compact, multiplication by each fixed
torus element and the quotient map are continuous, and the union is
finite.

`model_degreeCorankOnePolynomialIntegrand_support_subset` chooses one
bound `b` for the model vector and proves that the support in every
degree `d` is contained in this carrier. A nonzero degree-restricted
value has total degree `d` and a nonzero Laurent value. The exponent
bound therefore places its Iwasawa tuple in `boundedDegreeExponents`.
The actual Iwasawa decomposition identifies its quotient class with the
image of its integral factor; the proof checks the defining quotient
relation directly.

`model_degreeCorankOnePolynomialIntegrand_hasCompactSupport` derives
compact support from this containment. The local field is Hausdorff,
and the upper-unipotent subgroup is closed, so its left quotient is
Hausdorff. Thus the closure of the support still lies in the compact
carrier. `model_degreeCorankOnePolynomialIntegrand_eq_zero_below`
uses the same bound and the empty-tuple lemma to prove that every
degree integrand with `d < (n+1)*b` is identically zero.

`model_degreeCorankOnePolynomialSpan_finite` combines the same compact
carrier with the existing finite-span theorem for compact quotient support.
Thus every degree integrand has a finite-dimensional actual value span;
this fact is concluded rather than assumed of the representation.

## Normalized integration

`degreeCorankOneModelIntegrand_hasCompactSupport` specializes the
compact-support theorem to the existing model integrand, obtaining its
uniformizer and integer-conductor character from
`IsJacquetNormalization`.

`degreeCorankOneModelIntegrand_isScalarIntegrable` combines this
conclusion with the previously defined scalar integration adapter for
smooth model vectors and the normalized quotient measure. Local
constancy follows from smoothness and the unit-trivial absolute value.
Regularity of the normalized measure gives finiteness on compact sets.
The conclusion is integrability after every complex linear functional
on the actual span of the degree integrand's range. It imposes no
topology on the Laurent coefficient space, and has no compact-support
premise.

## Provenance

These are internal deductions from the published actual Iwasawa
decomposition, spherical Laurent support and invariance, general-field
smooth root bound, compactness of the integral subgroup, quotient
topology, and scalar integration constructions. The proof explicitly
constructs the finite exponent set and compact carrier. It invokes no
unproved essential-vector, factor-comparison, or conductor conclusion.
