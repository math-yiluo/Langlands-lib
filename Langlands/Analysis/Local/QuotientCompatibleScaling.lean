import Langlands.Analysis.Local.QuotientAutomorphismProof
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Compatible quotient measures for right-invariant subgroup measures

The Library's positive lifting (`realQuotientPositiveLifting`) and the uniqueness of compatible
quotient measures built on it (`IsCompatible.eq_smul_of_subgroup_smul`) take a subgroup measure
that is a left Haar measure and right invariant at the same time. This module removes the left
invariance: the subgroup measure `μH` is only right invariant, finite on compacts and positive on
open sets, as the centralizer measures of the simple trace formula are.

* `exists_compactNormalization_of_isMulRightInvariant`,
  `exists_positiveLifting_of_isMulRightInvariant`: every real compactly supported continuous
  function on `H \ G` is the fiber average of a compactly supported continuous function on `G`.
* `IsCompatible.smul_eq_smul`: if `ν₁` is compatible with `(μ₁, μH₁)`, `ν₂` with `(μ₂, μH₂)`,
  `μ₂ = a • μ₁` and `μH₂ = b • μH₁`, then `b • ν₂ = a • ν₁`.
* `IsCompatible.unique`: a compatible quotient measure is determined by the pair it is compatible
  with.
* `exists_eq_smul_of_isMulRightInvariant`: two right-invariant measures on a locally compact second
  countable group, finite on compacts and positive on open sets, differ by a positive scalar.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set
open scoped NNReal ENNReal CompactlySupported

universe u

private theorem quotient_mk_subgroup_mul_eq {G : Type u} [Group G]
    (H : Subgroup G) (h : H) (g : G) :
    Quotient.mk (QuotientGroup.rightRel H) (h.val * g) =
      Quotient.mk (QuotientGroup.rightRel H) g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev]

section Lifting

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace H] [BorelSpace H] (μH : Measure H)
  [IsMulRightInvariant μH] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]

include hH in
/-- **Compact normalization** for a right-invariant subgroup measure: for a compact set `K` of
cosets there is a nonnegative `f ∈ C_c(G, ℝ)` whose fiber integral is `1` over `K`. -/
theorem exists_compactNormalization_of_isMulRightInvariant
    (K : Set (LeftQuotient H)) (hK : IsCompact K) :
    ∃ f : C_c(G, ℝ), (∀ x, 0 ≤ f x) ∧
      ∀ g : G, Quotient.mk (QuotientGroup.rightRel H) g ∈ K →
        (∫ h : H, f (h.val * g) ∂μH) = 1 := by
  obtain ⟨C, hC, hCK⟩ := leftQuotient_exists_isCompact_image H hH hK
  obtain ⟨b, hbC, hbc, _, hb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hC isOpen_univ (subset_univ C)
  let b₀ : C_c(G, ℝ) := ⟨b, hbc⟩
  let A := quotientAverageReal H μH b₀
  have hAc : Continuous A := continuous_quotientAverageReal H hH μH b₀
  have hApos : ∀ q ∈ K, 0 < A q := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hCK ▸ hq
    change 0 < ∫ h : H, b₀ (h.val * x) ∂μH
    apply integral_pos_of_integrable_nonneg_nonzero
      (b₀.continuous.comp (continuous_subtype_val.mul_const x))
      (integrable_subgroup_mul H hH μH b₀ x) (fun h => (hb (h.val * x)).1)
      (x := (1 : H))
    change b ((1 : H).val * x) ≠ 0
    simpa only [OneMemClass.coe_one, one_mul, hbC hx, Pi.one_apply] using
      (one_ne_zero : (1 : ℝ) ≠ 0)
  obtain ⟨ε, hε, hεA⟩ := hK.exists_forall_le' hAc.continuousOn hApos
  let d : G → ℝ := fun g => max ε (A (leftQuotientMap H g))
  have hd : Continuous d := continuous_const.max (hAc.comp continuous_quotient_mk')
  have hdpos : ∀ g, 0 < d g := fun g => lt_of_lt_of_le hε (le_max_left _ _)
  let f : C_c(G, ℝ) :=
    { toFun := fun g => b₀ g / d g
      continuous_toFun := b₀.continuous.div hd (fun g => ne_of_gt (hdpos g))
      hasCompactSupport' := by
        simpa only [Pi.mul_def, div_eq_mul_inv] using
          (b₀.hasCompactSupport.mul_right (f' := fun g => (d g)⁻¹)) }
  refine ⟨f, fun g => div_nonneg (hb g).1 (hdpos g).le, ?_⟩
  intro g hg
  have hdf (h : H) : d (h.val * g) = d g := by
    simp only [d, leftQuotientMap_apply, quotient_mk_subgroup_mul_eq]
  change (∫ h : H, b₀ (h.val * g) / d (h.val * g) ∂μH) = 1
  simp_rw [hdf]
  rw [integral_div]
  change A (Quotient.mk _ g) / max ε (A (Quotient.mk _ g)) = 1
  rw [max_eq_right (hεA _ hg)]
  exact div_self (ne_of_gt (hApos _ hg))

include hH in
/-- **Positive lifting** for a right-invariant subgroup measure: every `φ ∈ C_c(H \ G, ℝ)` is the
fiber average `g ↦ ∫ f (h g) dμH(h)` of some `f ∈ C_c(G, ℝ)`, nonnegative when `φ` is. -/
theorem exists_positiveLifting_of_isMulRightInvariant (φ : C_c(LeftQuotient H, ℝ)) :
    ∃ f : C_c(G, ℝ),
      (∀ g : G, (∫ h : H, f (h.val * g) ∂μH) =
        φ (Quotient.mk (QuotientGroup.rightRel H) g)) ∧
      ((∀ q, 0 ≤ φ q) → ∀ x, 0 ≤ f x) := by
  obtain ⟨b, hb, hbK⟩ := exists_compactNormalization_of_isMulRightInvariant H hH μH
    (tsupport φ) φ.hasCompactSupport
  let f : C_c(G, ℝ) :=
    { toFun := fun g => φ (leftQuotientMap H g) * b g
      continuous_toFun := (φ.continuous.comp continuous_quotient_mk').mul b.continuous
      hasCompactSupport' := b.hasCompactSupport.mul_left }
  refine ⟨f, ?_, fun hφ g => mul_nonneg (hφ _) (hb _)⟩
  intro g
  change (∫ h : H, φ (leftQuotientMap H (h.val * g)) * b (h.val * g) ∂μH) = _
  simp_rw [leftQuotientMap_apply, quotient_mk_subgroup_mul_eq]
  rw [integral_const_mul]
  by_cases hg : Quotient.mk (QuotientGroup.rightRel H) g ∈ tsupport φ
  · rw [hbK g hg, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]

end Lifting

section Scaling

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
variable {H : Subgroup G} (hH : IsClosed (H : Set G)) [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

include hH in
/-- **Scaling of compatible quotient measures.** Let `ν₁` be compatible with `(μ₁, μH₁)` and `ν₂`
with `(μ₂, μH₂)`, where `μH₁` is right invariant, finite on compacts and positive on open sets. If
`μ₂ = a • μ₁` and `μH₂ = b • μH₁`, then `b • ν₂ = a • ν₁`. -/
theorem IsCompatible.smul_eq_smul {μ₁ μ₂ : Measure G} {μH₁ μH₂ : Measure H}
    [IsMulRightInvariant μH₁] [IsFiniteMeasureOnCompacts μH₁] [μH₁.IsOpenPosMeasure]
    [IsMulRightInvariant μH₂] {ν₁ ν₂ : Measure (LeftQuotient H)}
    (h₁ : IsCompatible H μ₁ μH₁ ν₁) (h₂ : IsCompatible H μ₂ μH₂ ν₂) {a b : ℝ≥0}
    (ha : μ₂ = a • μ₁) (hb : μH₂ = b • μH₁) : b • ν₂ = a • ν₁ := by
  have := leftQuotient_t2Space H hH
  have := leftQuotient_locallyCompactSpace (G := G) H
  have : ν₁.Regular := h₁.regular
  have : ν₂.Regular := h₂.regular
  have : (b • ν₂).Regular := Measure.Regular.smul ENNReal.coe_ne_top
  have : (a • ν₁).Regular := Measure.Regular.smul ENNReal.coe_ne_top
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  obtain ⟨f, hf, -⟩ := exists_positiveLifting_of_isMulRightInvariant H hH μH₁ φ
  have havg₁ : quotientAverageReal H μH₁ f = φ := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have havg₂ : quotientAverageReal H μH₂ f = fun q => (b : ℝ) * φ q := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [quotientAverageReal_mk, hb, integral_smul_nnreal_measure, hf, NNReal.smul_def,
        smul_eq_mul]
  calc
    (∫ q, φ q ∂(b • ν₂)) = (b : ℝ) * ∫ q, φ q ∂ν₂ := by
      rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    _ = ∫ q, quotientAverageReal H μH₂ f q ∂ν₂ := by rw [havg₂, integral_const_mul]
    _ = ∫ g, f g ∂μ₂ := h₂.integral_quotientAverageReal f f.continuous f.hasCompactSupport
    _ = (a : ℝ) * ∫ g, f g ∂μ₁ := by
      rw [ha, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    _ = (a : ℝ) * ∫ q, φ q ∂ν₁ := by
      rw [← h₁.integral_quotientAverageReal f f.continuous f.hasCompactSupport, havg₁]
    _ = ∫ q, φ q ∂(a • ν₁) := by
      rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

include hH in
/-- **Uniqueness of compatible quotient measures**: two quotient measures compatible with the
same pair `(μG, μH)`, for `μH` right invariant, finite on compacts and positive on open sets, are
equal. -/
theorem IsCompatible.unique {μG : Measure G} {μH : Measure H}
    [IsMulRightInvariant μH] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    {ν₁ ν₂ : Measure (LeftQuotient H)}
    (h₁ : IsCompatible H μG μH ν₁) (h₂ : IsCompatible H μG μH ν₂) : ν₁ = ν₂ := by
  have h := h₁.smul_eq_smul hH h₂ (a := 1) (b := 1) (one_smul _ _).symm (one_smul _ _).symm
  rwa [one_smul, one_smul, eq_comm] at h

end Scaling

/-- **Uniqueness of right Haar measure**: on a locally compact second countable group, two right
invariant measures that are finite on compacts and positive on open sets differ by a nonzero
scalar `c : ℝ≥0`. The proof applies Mathlib's uniqueness of left Haar measure to the inverse
measures `μ.inv`. -/
theorem exists_eq_smul_of_isMulRightInvariant {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ μ' : Measure G)
    [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [μ'.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ'] [μ'.IsOpenPosMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ' = c • μ := by
  have : μ.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have : μ'.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  refine ⟨haarScalarFactor μ'.inv μ.inv, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ?_⟩
  have h := isMulLeftInvariant_eq_smul μ'.inv μ.inv
  calc
    μ' = μ'.inv.inv := μ'.inv_inv.symm
    _ = (haarScalarFactor μ'.inv μ.inv • μ.inv).inv := by rw [← h]
    _ = haarScalarFactor μ'.inv μ.inv • μ := by
      rw [Measure.inv, Measure.map_smul _ measurable_inv.aemeasurable]
      exact congrArg _ μ.inv_inv

end Langlands.QuotientIntegration
