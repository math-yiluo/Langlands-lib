# Left translation of the integrated isometric action

`IntegratedActionLeftTranslationStatement` concerns the existing bounded
operator `integratedIsometricAction`. Let `G` be a group with a measurable
multiplication and a left invariant measure `μ`, and let `E` be a complete
complex normed space. Let `π` be a group homomorphism into the continuous
complex linear endomorphisms of `E`, preserving every vector norm, with every
orbit explicitly almost everywhere strongly measurable for `μ`.

For an actual integrable scalar function `f`, a vector `x`, and `p : G`, the
proposition asserts both integrability of the translated weighted orbit and
the literal equality

`π(p)(integratedIsometricAction(μ,π,f)(x))`
`= ∫ y, f(p⁻¹*y) • π(y)x ∂μ`.

The group and vector space universes are independent. No topology on `G`,
Haar regularity, nonzero measure, right invariance, inversion invariance,
unimodularity, finite measure, separability, or smoothness is assumed.
Inversion is used as a group operation; its measurability is unnecessary
because `p⁻¹` is fixed when translating. Orbit measurability remains an
explicit premise of the original operator construction.

This is an internal change of variables statement derived from the public
Bochner operator constructor and Mathlib's left translation identities.
The intended proof first establishes integrability using
`Integrable.comp_mul_left` for the scalar function and the constructor's
integrable norm majorant. The continuous linear map `π(p)` commutes with the
original Bochner integral. Its linearity and the group homomorphism identity
identify the resulting integrand with
`f(p⁻¹*(p*g)) • π(p*g)x`.
Left invariance, in the form `integral_mul_left_eq_self`, then substitutes
`y = p*g` without changing the measure.

For the inverse kernel `f(g) = κ(g⁻¹)`, the translated weight simplifies to
`κ(y⁻¹*p)`. Consequently this equality is the required algebraic bridge from
an actual integrated vector to the convolution with its original orbit.
This application still needs integrability of the inverse kernel. Smooth
convolution, smoothness of the resulting orbit, normalized kernel existence,
density, and automorphic tensor comparisons are separate analytic obligations.
This file supplies the exact proposition and no proof.
