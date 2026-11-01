# The reflection `[v] ↦ [w v^ι]` of the small quotient

Author: Worker 1037.

This module supplies derived measure-theoretic facts for the change of variables
in the transformed small integral of JPSS (1983), Section 4.9. Here `w` is the long
Weyl element and `ι` is the inverse transpose.

## The automorphism and the quotient map

`mulEquivHaarChar_eq_one_of_involutive` shows that an involutive continuous group
automorphism has Haar modulus one: its square is the identity.

`reflectionAut n` is the continuous automorphism `g ↦ w g^ι w` of `GL_(n+1)`.
`reflectionAut_involutive` shows it is an involution, and `reflectionAut_mem_iff`
shows it maps the upper unipotent subgroup onto itself, via the published
`reflectedUnipotent`.

`reflectionQuotient n` composes the induced quotient homeomorphism with right
translation by `w`. `reflectionQuotient_mk` shows it sends `[g]` to `[w g^ι]`, and
`reflectionQuotient_involutive` shows it is an involution.

## Determinant slices

`abv_det_weylLong_mul_inverseTranspose` gives `|det(w g^ι)| = |det g|⁻¹` for every
absolute value. Hence `reflectionQuotient_mem_determinantSlice` shows that the
reflection exchanges the determinant slices `k` and `-k`.

## Measure preservation

`measurePreserving_reflectionQuotient` concerns the canonical p-adic structures.
Every compatible quotient measure for the integral-points normalized Haar measures
of `GL_(n+1)` and `N_(n+1)` is preserved by the reflection. The published scaling
law `compatibleQuotientAutomorphismScaling` multiplies the measure by the ratio of
Haar moduli, and both moduli are one. Right translation by `w` preserves every
compatible measure.

`setIntegral_determinantSlice_reflectionQuotient` records the resulting change of
variables `∫_{slice k} f = ∫_{slice -k} f ∘ reflection`.
