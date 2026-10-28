# Radius-weighted power bounds and finite monomial bounds

Worker 56 defines the weighted power predicate and proves its basic calculus.
The finite-tuple argument adapts Worker 36's published unit-radius
`StrictTateAlgebra.hasBoundedMonomials_iff_pow_bound`.

For a normed ring \(A\), real radius \(r\), and element \(a\),
`Langlands.Analytic.HasRadiusBoundedPowers r a` means that there exists one
real constant \(C>0\) such that
\[
                     \|a^n\|\le C r^n\qquad(n\ge0).
\]
The definition is meaningful for any real \(r\); the applications in this
module use positive radii. Exponent zero is included, so the bound also controls
the actual norm of the target unit. No normalized-unit or nonzero-ring
assumption is imposed.

This is an internal predicate and elementary norm calculus. Its affinoid
motivation is Berkovich's 2009 Trieste lectures, Fact 2.1.4(i), printed/PDF
page 7: the source gives the corresponding power estimate at the spectral
radius for a nonnilpotent element of an affinoid algebra. Exercise 2.1.5(i),
printed/PDF pages 7–8, and Definition 2.1.6(i), printed/PDF page 8, give the
weighted-series evaluation context. None of those affinoid implications is
assumed or proved here. The registered source is
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

The radius-one predicate agrees with the existing `HasBoundedPowers`.
Increasing a nonnegative radius preserves the condition. Nilpotents satisfy
it for every strictly positive radius: choose a vanishing power \(d\), and
bound the finitely many earlier values \(\|a^i\|/r^i\) by one plus their sum.
Every later power is zero. A bounded ring homomorphism preserves the same
radius; multiply the original constant by a positive norm-bound constant
for the map.

`HasRadiusBoundedPowers.spectrum_le` proves the easy spectral direction for
every normed commutative ring. If a bounded multiplicative seminorm \(x\)
satisfied \(x(a)>r>0\), the powers of \(x(a)/r>1\) would be unbounded.
Multiplicativity, the spectrum point's domination by the actual ring norm,
and the weighted power bound instead bound all these powers by \(C\).
No completeness or affinoid presentation is used. The converse spectral
implication remains a separate theorem obligation.

In namespace `GeneralizedTateAlgebra`,
`HasBoundedMonomials.radiusBoundedPowers` specializes an existing weighted
monomial bound to the finitely supported exponent supported at one variable.
For a finite index type, `hasBoundedMonomials_iff_radiusBoundedPowers` proves
the converse as well. Choose constants \(C_i>0\) for the individual coordinates
and use
\[
        D=\max\bigl(1,\max(\|1\|,\prod_i C_i)\bigr).
\]
For a nonempty index type, the norm of each full product is bounded by the
product of the individual power bounds, which separates into
\( (\prod_i C_i)\prod_i r_i^{d_i}\).
The empty index type is handled separately using \(D\ge\|1\|\).
Thus the proof includes empty tuples, zero rings, and units with unnormalized
norm. Only the finite-tuple converse needs finiteness; the forward
single-coordinate implication works for arbitrary index types.

The power lemmas require a normed ring; the map, spectrum and monomial lemmas
require normed commutative rings. The index and target universes are independent.
There is no ultrametricity, scalar field, completeness, value-group, reducedness,
or proper-ideal assumption. This module supplies no converse from spectral
inequalities, analytic-domain factorization, or geometric site construction.
