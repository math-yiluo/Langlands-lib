# Smoothing of `L²([G])` classes by adelic test kernels

Module `Langlands.Global.AdelicCanonicalL2Smoothing` studies the right convolution of classes of
`L²([G])` by compactly supported kernels on `G(𝔸)`, for the canonical quotient
`[G] = A_G G(F) \ G(𝔸)` (`RestrictionSplitCentre.CanonicalQuotient`) with its canonical measure
`μ = RestrictionSplitCentre.canonicalMeasure F G`. Write `Γ = canonicalRationalSubgroup F G`
(that is `A_G G(F)`), `R` for the right regular representation
`canonicalL2RightAction F G centralSplitTorusCharacter hG` and `dg` for the Haar measure
`Measure.haar` of `G(𝔸)`.

| Declaration | Kind | Source |
| --- | --- | --- |
| `RestrictionSplitCentre.canonicalL2Pullback` | definition | internal |
| `measurable_canonicalL2Pullback`, `canonicalL2Pullback_mul` | theorems | internal |
| `RestrictionSplitCentre.canonicalL2Smoothing` | definition | Mœglin–Waldspurger I.2.5 |
| `canonicalL2Smoothing_mul` | theorem | internal |
| `canonicalSubgroupHaarMeasure_sigmaFinite` | theorem | internal |
| `exists_canonicalConvolutionKernel` | theorem | internal |
| `locallyIntegrable_canonicalL2Pullback` | theorem | internal |
| `isAdelicSmoothFunction_canonicalL2Smoothing` | theorem | Mœglin–Waldspurger I.2.5 |
| `canonicalL2IntegratedAction`, `canonicalL2IntegratedAction_apply` | definition, theorem | internal |
| `canonicalL2IntegratedAction_ae_eq` | theorem | internal |
| `canonicalSubgroupConjugateGrowth` | theorem | Mœglin–Waldspurger I.2.4 |
| `exists_canonicalL2Smoothing_bound` | theorem | Mœglin–Waldspurger I.2.5, Lemma (b) |
| `out_mk_eq`, `eq_of_ae_eq_out` | theorems | internal |
| `canonicalL2RightAction_ae_eq`, `inner_canonicalL2RightAction` | theorems | internal |
| `starProjection_canonicalL2RightAction`, `starProjection_canonicalL2IntegratedAction` | theorems | internal |
| `quasiMeasurePreserving_mk` | theorem | Weil's integration formula |
| `canonicalL2Pullback_ae_eq`, `canonicalL2Smoothing_eq_rightConvolution` | theorems | internal |
| `hasModerateGrowthFunction_canonicalL2Smoothing` | theorem | Mœglin–Waldspurger I.2.5, Lemma (b) |

All declarations are in the namespace `Langlands.Global.RestrictionSplitCentre`.

## Sources

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf` (file SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`). In I.2.4, Lemma (a)(i),
pp. 25–26, the count `∑_{γ ∈ G(k)} 1_C(x⁻¹ γ y) ≤ c ‖x‖^r` gives a corresponding bound for the
integral over `G(k) Z_G`. In I.2.5, Lemma (b), p. 27, right convolution `δ(f)` by a smooth compactly
supported function gives smooth functions of moderate growth for square-integrable inputs.

## Definitions

- `canonicalL2Pullback v x = v (mk x)` pulls back the chosen representative (the coercion
  `Lp ℂ 2 μ → ([G] → ℂ)`) of `v` to `G(𝔸)`.
- `canonicalL2Smoothing h v = rightConvolution F G h (canonicalL2Pullback v)` is the function
  `x ↦ ∫ h(a) v(mk(x a)) da`.
- `canonicalL2IntegratedAction hG h hh`, for integrable `h`, is the bounded operator
  `v ↦ ∫ h(g) • R g v dg` (`Langlands.Analysis.integratedIsometricAction` for the bounded right
  action `canonicalL2BoundedRightAction hG`).

## Results

1. `canonicalSubgroupHaarMeasure_sigmaFinite` uses local compactness and second countability of
   the closed subgroup `Γ` to show that its canonical Haar measure is σ-finite.
   `exists_canonicalConvolutionKernel` applies
   `quotientConvolutionKernel` to `Γ`, the canonical measures and the Weil compatibility
   `canonicalMeasure_isCompatible`, with finite volume from
   `connectedReductiveQuotientFiniteVolume`. For `f ∈ C_c(G(𝔸))` this gives a continuous family
   of kernel vectors `v_x ∈ L²([G])` with
   `⟪v_x, φ⟫ = ∫ f(a) φ(mk(x a)) da`, and
   `‖v_x‖² ≤ M ∫‖f‖ · μ_Γ(x S x⁻¹)` for `M ≥ ‖f‖∞` and
   `S = tsupport f · (tsupport f)⁻¹`. Taking `f` to be a cutoff equal to one on a given compact set
   gives `locallyIntegrable_canonicalL2Pullback`.
2. `isAdelicSmoothFunction_canonicalL2Smoothing` applies `adelicRightConvolutionDifferentiation`
   to the measurable, locally integrable pullback and an adelic test function `h`.
   `canonicalL2Smoothing_mul` inherits left invariance under `Γ` from the pullback.
3. `canonicalL2IntegratedAction_ae_eq` shows that the class
   `canonicalL2IntegratedAction hG h hh v` is represented `μ`-almost everywhere by
   `y ↦ canonicalL2Smoothing h v y.out` by `integratedTranslationPointwise` for
   the action of `G(𝔸)` on `[G]` by right translation, which preserves `μ` by
   `canonicalMeasure_rightInvariant`.
4. `canonicalSubgroupConjugateGrowth` transfers the bound
   `PositiveRealTorus.adelicPositiveRationalConjugateGrowth_allPoints` from
   `Langlands.Global.AdelicQuotientConvolutionGrowth` to the canonical measure on `Γ`. That measure
   is the pushforward of `intrinsicPositiveRationalSubgroupHaarMeasure` along the identification of
   the two subgroups. The intrinsic measure equals `positiveRationalSubgroupHaarMeasure` for any
   splitting of the canonical torus. For `f ∈ C_c(G(𝔸))` and `0 < N`,
   `exists_canonicalL2Smoothing_bound` then gives
   `‖canonicalL2Smoothing f v x‖ ≤ C · adelicHeight(x)^m · ‖v‖` for all `v` and all `x` by
   Cauchy–Schwarz against the kernel vectors. `hasModerateGrowthFunction_canonicalL2Smoothing` deduces
   `HasModerateGrowthFunction F G rho`, with `adelicHeight = c · adelicSourceNorm`
   (`adelicHeight_eq_scalar_mul_sourceNorm`). For `N = 0`, `G(𝔸)` is a single point
   (`isClosedEmbedding_adelicMatrix`) and the bound is a constant.
5. By `out_mk_eq`, a left `Γ`-invariant function takes the same value at `x` and at the
   representative `(mk x).out`. By `eq_of_ae_eq_out`, two continuous left `Γ`-invariant functions
   `u₁, u₂` with `u₁ ∘ out = u₂ ∘ out` `μ`-almost everywhere are equal. Their descents to `[G]`
   are continuous by `LeftCosetSpace.continuous_lift` and `μ` is positive on nonempty open sets by
   `canonicalMeasure_isOpenPosMeasure`.
6. `canonicalL2RightAction_ae_eq` transports the representative `u ∘ out` of `v` to
   `y ↦ u(y.out g)` for `R g v` when `u` is left `Γ`-invariant. By
   `inner_canonicalL2RightAction`, `R g` preserves inner products. If `V` is invariant under
   every `R g`, the identity `⟪w, R g z⟫ = ⟪R g⁻¹ w, z⟫` for `w ∈ V`, `z ∈ Vᗮ` gives invariance
   of `Vᗮ` as well. Thus the orthogonal projection commutes with every `R g` by
   `starProjection_canonicalL2RightAction` and with the Bochner integral of the weighted orbit
   by `starProjection_canonicalL2IntegratedAction`.
7. `quasiMeasurePreserving_mk` shows that `mk : G(𝔸) → [G]` pulls `μ`-null sets back to Haar-null
   sets. By Weil's formula for measurable nonnegative functions
   (`IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal`), the Haar measure of `mk⁻¹ s` is
   the integral over `[G]` of a function vanishing off `s`. If `v` is represented by `u ∘ out`
   with `u` left `Γ`-invariant, `canonicalL2Pullback_ae_eq` shows that the pullback of `v` agrees
   with `u` Haar-almost everywhere. Since left translation preserves Haar measure,
   `canonicalL2Smoothing_eq_rightConvolution` gives equality of `canonicalL2Smoothing h v` and
   `rightConvolution F G h u` at every point.
