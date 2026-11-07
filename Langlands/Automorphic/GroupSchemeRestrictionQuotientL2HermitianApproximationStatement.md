# Hermitian approximation of the right action on `L²([G])`

Author: Worker 112.

`Langlands.Global.RestrictionSplitCentre.QuotientL2HermitianApproximationStatement`
asks for an approximate identity for the right action on `L²` of the
restriction split-centre quotient `RestrictionSplitCentre.Quotient F G S j`.
This quotient has the shape `[G] = A_G G(F) \ G(A_F)` of Getz--Hahn
(2.20)--(2.21) (`getz-hahn-2024-automorphic-representations`, printed
pp. 68--69). The space is `Lp ℂ 2 (quotientHaarMeasure F G S j)` with the
published canonical quotient measure. The operators are exactly the published
integrated actions `rationalQuotientL2IntegratedAction` of
`GroupSchemeRestrictionQuotientL2Continuity`. It is the `[G]` counterpart of
the published positive-torus `GroupSchemeQuotientL2HermitianApproximationStatement`.

## Hypotheses

The proposition quantifies over:

- a number field `F : Type`, and a group scheme `G` over `Spec F` whose
  underlying scheme is affine and locally of finite type;
- a commutative group scheme `S` over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`, which define the published
  quotient `Quotient F G S j`;
- a commutative group scheme `T` over `F` and `i : T.toGrp ⟶ G` with
  `h : subgroup F G S j = imageSubgroup F T G i`, injective character
  restriction `hi` with finite-index range, `hc : IsCentral i` and
  `hT : IsSplitTorus T.toGrp`;
- right invariance of Haar measure on `normOneSubgroup F G` (an instance
  argument), and any proof `hInv'` of
  `QuotientRightInvariant F G (quotientHaarMeasure F G S j)`.

These are exactly the hypotheses under which the published module constructs
the jointly continuous action and its integrated operators. No reductivity,
finite volume or smoothness is assumed.

## Conclusion

Write `μG` for Mathlib's left Haar measure `Measure.haar` on the adelic points
`AdelicGroupPoints F G`. The integrated operators integrate against the right
Haar measure `μG.inv`. The proposition asserts that there exist real functions
`f n` on `G(A_F)` and proofs `hf n` of their `μG.inv`-integrability with:

- each `f n` continuous, compactly supported and nonnegative, with
  `∫ f n ∂μG.inv = 1`;
- `f n a = (Measure.modularCharacter a⁻¹ : ℝ) * f n a⁻¹` for every `a`;
- for every neighbourhood `U` of the identity, `tsupport (f n) ⊆ U` for all
  large `n`;
- the operators
  `A n = rationalQuotientL2IntegratedAction F G hInv' h hi hc hT μG.inv (f n) (hf n).ofReal`,
  with complex weights `a ↦ (f n a : ℂ)`, are symmetric with operator norm at
  most one;
- `A n φ → φ` for every `φ` in `L²([G])`.

## Source

Getz--Hahn section 9.3, printed p. 246 (PDF p. 258), define a Dirac sequence
on `A_G \ G(A_F)`: nonnegative functions in `C_c^∞(A_G \ G(A_F))` with
supports eventually inside every relatively compact neighbourhood of `1`, with
`f_n(x) = f_n(x⁻¹) δ_G⁻¹(x)`, and with integral one. They note that
`R(f_n) φ → φ` and that `R(f_n)` is self-adjoint on a unitary representation.
The modular quasi-character `δ_G` is their (3.6)--(3.8), section 3.2,
printed pp. 81--82 (PDF pp. 97--98). The comparison of their `δ_G` with
Mathlib's `Measure.modularCharacter`, and of their right Haar measure with
`μG.inv`, is explained in the published
`Langlands.Representation.Unitary.RightHaarHermitianApproximationStatement`.

The present proposition is a qualified continuous precursor of the source
assertion. The weights are continuous, not smooth, and they live on the full
group `G(A_F)` rather than on `A_G \ G(A_F)`. No descent of the weights to that
quotient group is asserted.

## Status

This module states the proposition and contains no proof. The intended proof
applies the published generic theorem
`Langlands.Analysis.rightHaarHermitianApproximation` to the published bounded
action `rationalQuotientL2BoundedRightAction`, whose operators are linear
isometries and whose orbits are continuous (`rationalQuotientL2OrbitMap`).
This is the same route as the published positive-torus proof
`groupSchemeQuotientL2HermitianApproximation`. A proof of this `[G]` statement
is a separate obligation. The statement asserts no smooth-vector density,
compactness, trace-class property or spectral decomposition.
