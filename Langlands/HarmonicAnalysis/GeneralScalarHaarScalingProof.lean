import Langlands.HarmonicAnalysis.GeneralHaarScalingStatement
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Residue-normalized scalar Haar scaling over general local fields

Intrinsic topology and regularity lemmas for every nonarchimedean local field,
including positive characteristic, followed by the scalar pushforward formula
for every additive Haar measure.
-/

open scoped NNReal ENNReal Pointwise
open MeasureTheory Set TopologicalSpace ValuativeRel

namespace Langlands.HarmonicAnalysis.GeneralLocalField

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The topology of a nonarchimedean local field is the topology of a proper
nontrivially normed field structure. -/
theorem properNormedField :
    ∃ N : NontriviallyNormedField F,
      @UniformSpace.toTopologicalSpace F
          (@PseudoMetricSpace.toUniformSpace F N.toPseudoMetricSpace) =
        ‹TopologicalSpace F› ∧
      @ProperSpace F N.toPseudoMetricSpace := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F) (Γ₀ := ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let N : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField (L := F) (Γ₀ := ValueGroupWithZero F)
  exact ⟨N, rfl, .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F⟩

/-- A nonarchimedean local field is second countable. -/
theorem secondCountableTopology : SecondCountableTopology F := by
  obtain ⟨N, hN, hP⟩ := properNormedField F
  have h := @secondCountable_of_proper F N.toPseudoMetricSpace hP
  rw [hN] at h
  exact h

/-- A nonarchimedean local field is sigma compact. -/
theorem sigmaCompactSpace : SigmaCompactSpace F := by
  have := secondCountableTopology F
  infer_instance

/-- A nonarchimedean local field is pseudometrizable. -/
theorem pseudoMetrizableSpace : PseudoMetrizableSpace F := by
  obtain ⟨N, hN, -⟩ := properNormedField F
  have h := @UniformSpace.pseudoMetrizableSpace F
    (@PseudoMetricSpace.toUniformSpace F N.toPseudoMetricSpace) inferInstance
  rw [hN] at h
  exact h

/-- A nonarchimedean local field is Hausdorff. -/
theorem t2Space : T2Space F := by
  obtain ⟨N, hN, -⟩ := properNormedField F
  have h : @T2Space F (@UniformSpace.toTopologicalSpace F
      (@PseudoMetricSpace.toUniformSpace F N.toPseudoMetricSpace)) := by
    let := N.toMetricSpace
    infer_instance
  rw [hN] at h
  exact h

/-- Every additive Haar measure on a nonarchimedean local field is regular. -/
theorem haarMeasure_regular [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] : μ.Regular := by
  have := sigmaCompactSpace F
  have := pseudoMetrizableSpace F
  infer_instance

/-- The valuation ring of a nonarchimedean local field is compact. -/
theorem isCompact_integer : IsCompact (𝒪[F] : Set F) :=
  IsNonarchimedeanLocalField.isCompact_closedBall F 1

/-- The valuation ring of a nonarchimedean local field is open. -/
theorem isOpen_integer : IsOpen (𝒪[F] : Set F) :=
  (valuation F).isOpen_integer

private theorem residueCard_mul_measure_maximalIdeal [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    (Nat.card 𝓀[F] : ℝ≥0∞) * μ (Subtype.val '' (𝓂[F] : Set 𝒪[F])) =
      μ (𝒪[F] : Set F) := by
  have := t2Space F
  let H := (𝓂[F]).toAddSubgroup
  have hme : MeasurableEmbedding (Subtype.val : 𝒪[F] → F) :=
    MeasurableEmbedding.subtype_coe (isOpen_integer F).measurableSet
  let ν := μ.comap (Subtype.val : 𝒪[F] → F)
  have : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ
    (f := (𝒪[F]).subtype.toAddMonoidHom) hme
  have : H.FiniteIndex := @AddSubgroup.finiteIndex_of_finite_quotient _ _ H
    (inferInstanceAs (Finite 𝓀[F]))
  have hH : MeasurableSet (H : Set 𝒪[F]) :=
    (IsLocalRing.isOpen_maximalIdeal 𝒪[F]).measurableSet
  have he := H.index_mul_measure hH ν
  change (Nat.card 𝓀[F] : ℝ≥0∞) * ν H = ν Set.univ at he
  change (Nat.card 𝓀[F] : ℝ≥0∞) *
    (μ.comap (Subtype.val : 𝒪[F] → F)) (H : Set 𝒪[F]) =
    (μ.comap (Subtype.val : 𝒪[F] → F)) Set.univ at he
  have hrange : Set.range (Subtype.val : 𝒪[F] → F) = (𝒪[F] : Set F) :=
    Set.ext (fun x => by simp)
  simpa only [hme.comap_apply, Set.image_univ, hrange, H, Submodule.coe_toAddSubgroup] using he

variable {F}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem smul_integer_eq (a : Fˣ) :
    a • (𝒪[F] : Set F) = {x | valuation F x ≤ valuation F a} := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (↑a⁻¹ : F) * x ∈ 𝒪[F] ↔ _
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    inv_mul_le_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 a.ne_zero)), mul_one]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem valuation_lt_one_iff {ϖ : Fˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ) (x : F) :
    valuation F x < 1 ↔ valuation F x ≤ valuation F ϖ := by
  refine ⟨fun hx => ?_, fun hx => hx.trans_lt hϖ.1⟩
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact zero_le
  obtain ⟨m, hm⟩ := hϖ.2 x hx0
  have h0 := GeneralLinear.Iwasawa.valuation_pos (valuation F) ϖ
  have hanti := zpow_right_strictAnti₀ h0 hϖ.1
  rw [hm] at hx ⊢
  have h1 : (0 : ℤ) < m := by
    rw [← zpow_zero (valuation F (ϖ : F))] at hx
    exact hanti.lt_iff_gt.mp hx
  calc valuation F (ϖ : F) ^ m ≤ valuation F (ϖ : F) ^ (1 : ℤ) :=
        hanti.antitone (by omega)
    _ = valuation F (ϖ : F) := zpow_one _

private theorem uniformizer_smul_integer {ϖ : Fˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ) :
    ϖ • (𝒪[F] : Set F) = Subtype.val '' (𝓂[F] : Set 𝒪[F]) := by
  rw [smul_integer_eq]
  ext x
  change valuation F x ≤ valuation F ϖ ↔ _
  rw [← valuation_lt_one_iff hϖ]
  constructor
  · intro hx
    have hxO : x ∈ 𝒪[F] := hx.le
    refine ⟨⟨x, hxO⟩, ?_, rfl⟩
    change (⟨x, hxO⟩ : 𝒪[F]) ∈ 𝓂[F]
    rw [IsLocalRing.mem_maximalIdeal]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hx
  · rintro ⟨x, hx, rfl⟩
    change x ∈ 𝓂[F] at hx
    rw [IsLocalRing.mem_maximalIdeal] at hx
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hx

private theorem distribHaarChar_eq_absUnits [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (q : ℕ) (hq : q = Nat.card 𝓀[F])
    (abv : AbsoluteValue F ℝ) {ϖ : Fˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ)
    (habvϖ : abv (ϖ : F) = (q : ℝ)⁻¹)
    (habv1 : ∀ x : F, valuation F x = 1 → abv x = 1) (a : Fˣ) :
    distribHaarChar F a = (Shahidi.absUnits abv a : ℝ≥0) := by
  have := haarMeasure_regular F μ
  have hO0 : μ (𝒪[F] : Set F) ≠ 0 :=
    ne_of_gt ((isOpen_integer F).measure_pos μ ⟨0, (𝒪[F]).zero_mem⟩)
  have hOtop : μ (𝒪[F] : Set F) ≠ ∞ := (isCompact_integer F).measure_ne_top
  have hq1 : 1 < q := by
    rw [hq]
    exact Finite.one_lt_card
  have hϖchar : distribHaarChar F ϖ = (q : ℝ≥0)⁻¹ := by
    have h := residueCard_mul_measure_maximalIdeal F μ
    rw [← uniformizer_smul_integer hϖ, ← distribHaarChar_mul μ, ← hq] at h
    have hp : (q : ℝ≥0∞) * ↑(distribHaarChar F ϖ) = 1 := by
      apply (ENNReal.mul_left_inj hO0 hOtop).mp
      simpa only [mul_assoc, one_mul] using h
    have hp' : (q : ℝ≥0) * distribHaarChar F ϖ = 1 := by
      exact ENNReal.coe_injective (by simpa only [ENNReal.coe_mul, ENNReal.coe_natCast,
        ENNReal.coe_one] using hp)
    have hq0 : (q : ℝ≥0) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hq1).ne'
    apply mul_left_cancel₀ hq0
    rw [mul_inv_cancel₀ hq0]
    exact hp'
  obtain ⟨m, hm⟩ := hϖ.2 a a.ne_zero
  have hval : valuation F ((ϖ ^ m : Fˣ) : F) = valuation F a := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hm]
  have hchar : distribHaarChar F a = distribHaarChar F (ϖ ^ m) := by
    apply ENNReal.coe_injective
    apply (ENNReal.mul_left_inj hO0 hOtop).mp
    rw [distribHaarChar_mul μ, distribHaarChar_mul μ,
      smul_integer_eq, smul_integer_eq, hval]
  have hunit : Shahidi.absUnits abv (a * ϖ⁻¹ ^ m) = 1 := by
    apply Units.ext
    apply Subtype.ext
    change abv ((a * ϖ⁻¹ ^ m : Fˣ) : F) = 1
    apply habv1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀,
      Units.val_inv_eq_inv_val, map_inv₀, hm, inv_zpow', ← zpow_add₀]
    · simp
    · exact (GeneralLinear.Iwasawa.valuation_pos (valuation F) ϖ).ne'
  have habs : Shahidi.absUnits abv a = Shahidi.absUnits abv ϖ ^ m := by
    have h := congrArg (· * Shahidi.absUnits abv ϖ ^ m) hunit
    simp only [map_mul, map_zpow, map_inv, one_mul] at h
    rw [← h, inv_zpow', mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hϖabs : (Shahidi.absUnits abv ϖ : ℝ≥0) = (q : ℝ≥0)⁻¹ := by
    apply NNReal.eq
    change abv (ϖ : F) = _
    rw [habvϖ, NNReal.coe_inv, NNReal.coe_natCast]
  rw [hchar, map_zpow, hϖchar, habs, Units.val_zpow_eq_zpow_val, hϖabs]

end Langlands.HarmonicAnalysis.GeneralLocalField

namespace Langlands.HarmonicAnalysis

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The exact published general-field scalar Haar scaling proposition. -/
theorem generalScalarHaarScalingStatement :
    GeneralScalarHaarScalingStatement.{uF} F := by
  intro q hq abv ϖ hϖ habvϖ habv1 _ _ μ _ a
  have := GeneralLocalField.haarMeasure_regular F μ
  ext s hs
  change (μ.map (fun x => a • x)) s = _
  rw [Measure.map_apply (measurable_const_smul a) hs, Set.preimage_smul,
    ← distribHaarChar_mul μ,
    GeneralLocalField.distribHaarChar_eq_absUnits μ q hq abv hϖ habvϖ habv1,
    map_inv, Units.val_inv_eq_inv_val, Measure.smul_apply]
  rfl

end Langlands.HarmonicAnalysis
