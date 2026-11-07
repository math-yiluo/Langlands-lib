# One Hermitian approximation on `L²([G])` and its a.e. cuspidal subspace

Author: Worker 112.

`Langlands.Global.RestrictionSplitCentre.QuotientFullAEL2HermitianApproximationStatement`
asks for one sequence of weights on `G(A_F)` whose integrated actions
approximate the identity both on `L²([G])` and on its published
almost-everywhere cuspidal subspace. Here `[G]` is the restriction split-centre
quotient `RestrictionSplitCentre.Quotient F G S j`, of the shape
`A_G G(F) \ G(A_F)` of Getz--Hahn (2.20)--(2.21)
(`getz-hahn-2024-automorphic-representations`, printed pp. 68--69). The
subspace is the published `quotientFullAEL2CuspidalSubmodule`, following
their (6.20)--(6.21) (printed p. 168). The same weights, group measure and
index serve both spaces. It is the `[G]` counterpart of the published
positive-torus `GroupSchemeFullAEL2HermitianApproximationStatement`.

## Hypotheses

The proposition quantifies over the data of
`QuotientL2HermitianApproximationStatement` (number field `F : Type`, affine
locally finite-type `G`, `S`, `j`, `T`, `i`, `h`, `hi` with finite-index
range, `hc`, `hT`, norm-one right invariance and `hInv'`). In addition it
takes `hPD : ParabolicDynamicStatement.{0}` and
`hG : IsConnectedReductive G`, the hypotheses of the published cuspidal
subspace. That subspace is defined by almost-everywhere vanishing of the
period along the unipotent radical of every proper rational parabolic; see
`GroupSchemeRestrictionFullAEL2.md`.

## Conclusion

Write `μG` for the left Haar measure on `AdelicGroupPoints F G` and
`Sq` for `quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT`. There exist
real functions `f n` with `μG.inv`-integrability proofs `hf n` such that:

- each `f n` is continuous, compactly supported and nonnegative, with
  `∫ f n ∂μG.inv = 1`, and
  `f n a = (Measure.modularCharacter a⁻¹ : ℝ) * f n a⁻¹`;
- for every neighbourhood `U` of the identity, `tsupport (f n) ⊆ U` for all
  large `n`;
- `A n` is the published `rationalQuotientL2IntegratedAction` and `B n` the
  published `quotientFullAEL2CuspidalIntegratedAction` (module
  `GroupSchemeRestrictionFullAEL2Continuity`), both with complex weight
  `a ↦ (f n a : ℂ)` against `μG.inv`;
- each `A n` and each `B n` is symmetric with operator norm at most one;
- `A n φ → φ` for every `φ` in `L²([G])`, and `B n ψ → ψ` for every `ψ` in
  `Sq`;
- `(B n ψ).val = A n ψ.val` for `ψ` in `Sq`;
- the published orthogonal projection
  `quotientFullAEL2CuspidalOrthogonalProjection` carries `A n φ` to
  `B n` of the projection of `φ`, and the published ambient projection
  `quotientFullAEL2CuspidalAmbientProjection` commutes with `A n`.

## Source

The source of the approximate identity is Getz--Hahn section 9.3, printed
p. 246 (PDF p. 258), with the modular quasi-character of section 3.2, printed
pp. 81--82; see `GroupSchemeRestrictionQuotientL2HermitianApproximationStatement.md`.
As there, the weights here are continuous and live on the full group
`G(A_F)`. This is a qualified continuous precursor of the source assertion,
with no descent to `A_G \ G(A_F)`.

## Status

This module states the proposition and contains no proof. The intended proof
takes the weights of `QuotientL2HermitianApproximationStatement` once and
transfers the cuspidal conclusions through the published inclusion identity
`quotientFullAEL2CuspidalIntegratedAction_val` and the published projection
laws `quotientFullAEL2CuspidalOrthogonalProjection_integratedAction` and
`quotientFullAEL2CuspidalAmbientProjection_integratedAction`. This follows the
published positive-torus proof `groupSchemeFullAEL2HermitianApproximation`. A
proof is a separate obligation. No smooth-vector density, compactness,
trace-class property or spectral decomposition is asserted.
