# Compatible quotient measures for right-invariant subgroup measures

Module `Langlands.Analysis.Local.QuotientCompatibleScaling`, namespace
`Langlands.QuotientIntegration`.

The Library's positive lifting `realQuotientPositiveLifting` and the uniqueness of compatible
quotient measures proved from it, `IsCompatible.eq_smul_of_subgroup_smul`, ask that the subgroup
measure `μH` be a left Haar measure that is also right invariant, which forces the subgroup to be
unimodular. The centralizer measures of the simple trace formula
(`GeneralLinearSimpleTraceFormulaStatement`) are only right invariant, finite on compacts and
positive on open sets. This module proves the lifting, the scaling and the uniqueness for such
measures, and the uniqueness of right-invariant measures up to a scalar.

## Statements

Throughout, `G` is a locally compact topological group, `H` a closed subgroup (`hH`), and
`LeftQuotient H` the space of cosets `H g` with the quotient topology.

- `exists_compactNormalization_of_isMulRightInvariant H hH μH K hK` for
  `[IsMulRightInvariant μH] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]` and a compact
  `K ⊆ H \ G`:

  `∃ f : C_c(G, ℝ), (∀ x, 0 ≤ f x) ∧ ∀ g : G, Quotient.mk _ g ∈ K → (∫ h : H, f (h.val * g) ∂μH) = 1`.

- `exists_positiveLifting_of_isMulRightInvariant H hH μH φ` for `φ : C_c(LeftQuotient H, ℝ)`:

  `∃ f : C_c(G, ℝ), (∀ g, (∫ h : H, f (h.val * g) ∂μH) = φ (Quotient.mk _ g)) ∧
    ((∀ q, 0 ≤ φ q) → ∀ x, 0 ≤ f x)`.

  These are the statements `RealQuotientCompactNormalization` and `RealQuotientPositiveLifting`
  (`QuotientMeasurePrerequisites`) for one group, with `[IsHaarMeasure μH] [μH.Regular]` replaced by
  `[IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]`.

- `IsCompatible.smul_eq_smul hH h₁ h₂ ha hb`: with `G` also measurable, for
  `h₁ : IsCompatible H μ₁ μH₁ ν₁`, `h₂ : IsCompatible H μ₂ μH₂ ν₂`, `μH₁` right invariant, finite on
  compacts and positive on open sets, `μH₂` right invariant, `ha : μ₂ = a • μ₁` and
  `hb : μH₂ = b • μH₁` with `a b : ℝ≥0`:

  `b • ν₂ = a • ν₁`.

  The two scalings used in the simple trace formula are special cases: scaling the subgroup measure
  only (`a = 1`) gives `c • ν₂ = ν₁` for `μH₂ = c • μH₁`, the case of
  `IsCompatible.eq_smul_of_subgroup_smul`; scaling the ambient measure only (`b = 1`) gives
  `ν₂ = c • ν₁` for `μ₂ = c • μ₁`.

- `IsCompatible.unique hH h₁ h₂ : ν₁ = ν₂` for two measures compatible with the same pair
  `(μG, μH)`, `μH` as above.

- `exists_eq_smul_of_isMulRightInvariant μ μ'`: on a locally compact second countable group with
  its Borel structure, for `μ`, `μ'` right invariant, finite on compacts and positive on open sets,

  `∃ c : ℝ≥0, c ≠ 0 ∧ μ' = c • μ`.

## Proofs

The lifting is the Library's proof of `realQuotientCompactNormalization` and
`realQuotientPositiveLifting` with the weaker hypotheses: a compact `C ⊆ G` mapping onto `K`
(`leftQuotient_exists_isCompact_image`), an Urysohn function `b` equal to `1` on `C`, its average
`A = quotientAverageReal H μH b`, continuous (`continuous_quotientAverageReal`, which needs only
finiteness on compacts) and positive on `K` (positivity on open sets, through
`integral_pos_of_integrable_nonneg_nonzero`), and `f = b / max ε A`. The lift of `φ` is
`f · (φ ∘ quotient map)`. Left invariance of `μH` is never used.

For the scaling, both sides are regular measures on the locally compact Hausdorff space `H \ G`
(`IsCompatible.regular`, `leftQuotient_t2Space`, `leftQuotient_locallyCompactSpace`), so by
`Measure.ext_of_integral_eq_on_compactlySupported` it suffices to compare the integrals of every
`φ ∈ C_c(H \ G, ℝ)`. Lift `φ` to `f` for `μH₁`; then the `μH₂`-average of `f` is `b φ`, and the
real Weil formula (`IsCompatible.integral_quotientAverageReal`) gives

`b ∫ φ dν₂ = ∫ f dμ₂ = a ∫ f dμ₁ = a ∫ φ dν₁`.

Uniqueness is the case `a = b = 1`. For right Haar uniqueness, `μ.inv` and `μ'.inv` are left Haar
measures (Mathlib's instances `inv.instIsMulLeftInvariant`, `IsFiniteMeasureOnCompacts.inv`,
`IsOpenPosMeasure.inv`), so `μ'.inv = c • μ.inv` with `c = haarScalarFactor μ'.inv μ.inv > 0`
(`isMulLeftInvariant_eq_smul`, `haarScalarFactor_pos_of_isHaarMeasure`), and inverting again gives
`μ' = c • μ`.

## Declarations, in order

- `quotient_mk_subgroup_mul_eq` (private): `H (h g) = H g`.
- `exists_compactNormalization_of_isMulRightInvariant`
- `exists_positiveLifting_of_isMulRightInvariant`
- `IsCompatible.smul_eq_smul`
- `IsCompatible.unique`
- `exists_eq_smul_of_isMulRightInvariant`

## Literature

The scaling of quotient measures and the uniqueness of right Haar measure are the standard facts
behind the remark of Getz–Hahn, *An introduction to automorphic representations* (2024), §18.4,
after Corollary 18.4.1 (printed p. 485), that the measure on `C_γ(𝔸_F) \ G(𝔸_F)` used for the orbital
integral is normalized to correspond to the Haar measures chosen on the group and on the
centralizer, the centralizer measure being the one used for the volume `τ(C_γ)`. The proofs here
follow the Library's existing quotient-measure files and do not follow a printed source.
