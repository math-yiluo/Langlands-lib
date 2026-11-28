import Langlands.HarmonicAnalysis.UnitConjugation.CharacteristicSize
import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentOrbitRescaling
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-! # Characteristic cutoffs and their constancy on large lattice cosets -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Metric Filter Function _root_.Topology
open scoped NNReal

variable {F A : Type*} [NontriviallyNormedField F] [NormedRing A] [NormedAlgebra F A]
  [FiniteDimensional F A] [CompleteSpace F] [IsUltrametricDist F]

/-- The open cone of points where the characteristic size is small relative to the norm. -/
def characteristicCone (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F A]
    [FiniteDimensional F A] (δ : ℝ) : Set A :=
  {x | (characteristicSize F x : ℝ) < δ * ‖x‖}

omit [IsUltrametricDist F] in
private theorem continuous_realCharacteristicSize : Continuous (fun x : A => (characteristicSize F x : ℝ)) :=
  continuous_subtype_val.comp continuous_characteristicSize

omit [IsUltrametricDist F] in
theorem isOpen_characteristicCone (δ : ℝ) : IsOpen (characteristicCone (A := A) F δ) :=
  isOpen_lt continuous_realCharacteristicSize (continuous_const.mul continuous_norm)

omit [CompleteSpace F] [IsUltrametricDist F] in
theorem smul_mem_characteristicCone_iff (δ : ℝ) {a : F} (ha : a ≠ 0) (x : A) :
    a • x ∈ characteristicCone F δ ↔ x ∈ characteristicCone F δ := by
  change (characteristicSize F (a • x) : ℝ) < δ * ‖a • x‖ ↔ (characteristicSize F x : ℝ) < δ * ‖x‖
  rw [characteristicSize_smul, NNReal.coe_mul, coe_nnnorm, norm_smul, mul_left_comm δ,
    mul_lt_mul_iff_right₀ (norm_pos_iff.mpr ha)]

omit [CompleteSpace F] [IsUltrametricDist F] in
theorem nilpotentAnnulus_subset_characteristicCone {d : F} (hd : 1 < ‖d‖) {δ : ℝ} (hδ : 0 < δ) :
    nilpotentAnnulus d A ⊆ characteristicCone F δ := by
  rintro x ⟨hx, _, hnil⟩
  change (characteristicSize F x : ℝ) < δ * ‖x‖
  rw [(characteristicSize_eq_zero_iff x).mpr hnil, NNReal.coe_zero]
  exact mul_pos hδ ((one_div_pos.mpr (zero_lt_one.trans hd)).trans_le hx)

omit [IsUltrametricDist F] in
/-- On a compact normalization set, a cone of sufficiently small relative
characteristic size is inside any given open neighborhood of the nilpotent points. -/
theorem exists_characteristicCone_inter_subset {K V : Set A} (hK : IsCompact K) (hV : IsOpen V)
    (hNil : ∀ x ∈ K, IsNilpotent x → x ∈ V) :
    ∃ δ > (0 : ℝ), K ∩ characteristicCone F δ ⊆ V := by
  by_cases hne : (K \ V).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (hK.diff hV).exists_isMinOn hne (continuous_realCharacteristicSize (F := F) (A := A)).continuousOn
    have hpos : (0 : ℝ) < characteristicSize F x := by
      rw [NNReal.coe_pos, pos_iff_ne_zero]
      exact fun hz => hx.2 (hNil x hx.1 ((characteristicSize_eq_zero_iff x).mp hz))
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : A → A)).continuousOn
    let δ := (characteristicSize F x : ℝ) / max 1 B
    have hm : 0 < max 1 B := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨δ, div_pos hpos hm, fun y hy => ?_⟩
    by_contra hyV
    have hyNorm : ‖y‖ ≤ max 1 B := (hB y hy.1).trans (le_max_right _ _)
    have hySize : (characteristicSize F y : ℝ) < δ * ‖y‖ := hy.2
    have hδ : 0 ≤ δ := (div_pos hpos hm).le
    have hle : δ * ‖y‖ ≤ (characteristicSize F x : ℝ) := by
      calc
        _ ≤ δ * max 1 B := mul_le_mul_of_nonneg_left hyNorm hδ
        _ = _ := div_mul_cancel₀ _ hm.ne'
    exact (not_lt_of_ge (hmin ⟨hy.1, hyV⟩)) (hySize.trans_le hle)
  · exact ⟨1, zero_lt_one, fun x hx => by
      by_contra hxV
      exact hne ⟨x, hx.1, hxV⟩⟩

private theorem characteristicSize_uniform_add {K : Set A} (hK : IsCompact K)
    (hPos : ∀ x ∈ K, 0 < characteristicSize F x) :
    ∃ ε > (0 : ℝ), ∀ x ∈ K, ∀ v : A, ‖v‖ < ε → characteristicSize F (x + v) = characteristicSize F x := by
  let Q : Set (A × A) := {z | characteristicSize F (z.1 + z.2) = characteristicSize F z.1}
  have hQ : K ×ˢ {(0 : A)} ⊆ interior Q := by
    rintro ⟨x, v⟩ ⟨hx, rfl⟩
    obtain ⟨U, hU, hUo, hxU⟩ := _root_.mem_nhds_iff.mp ((characteristicSize_spec (A := A) (F := F)).2 x (hPos x hx))
    apply mem_interior_iff_mem_nhds.mpr
    refine _root_.mem_nhds_iff.mpr ⟨Prod.fst ⁻¹' U ∩ (fun z : A × A => z.1 + z.2) ⁻¹' U, ?_,
      (hUo.preimage continuous_fst).inter (hUo.preimage (continuous_fst.add continuous_snd)), ?_⟩
    · rintro ⟨y, w⟩ ⟨hy, hw⟩
      exact (hU hw).trans (hU hy).symm
    · exact ⟨hxU, by simpa using hxU⟩
  obtain ⟨U, W, _, hWo, hKU, h0W, hUW⟩ := generalized_tube_lemma hK isCompact_singleton isOpen_interior hQ
  obtain ⟨ε, hε, hEmb⟩ := Metric.mem_nhds_iff.mp (hWo.mem_nhds (h0W (mem_singleton (0 : A))))
  refine ⟨ε, hε, fun x hx v hv => ?_⟩
  have hvW : v ∈ W := hEmb (by simpa only [mem_ball, dist_zero_right] using hv)
  exact show (x, v) ∈ Q from interior_subset (hUW (show (x, v) ∈ U ×ˢ W from ⟨hKU hx, hvW⟩))

variable [ProperSpace A] [IsUltrametricDist A]

/-- Outside a characteristic cone, every sufficiently large center and its
translates by a bounded lattice have the same norm and characteristic size. -/
def LargeCharacteristicCosetStatement (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F A]
    [FiniteDimensional F A] (d : F) (δ : ℝ) : Prop :=
  1 < ‖d‖ → 0 < δ → ∀ L : AddSubgroup A, IsCompact (L : Set A) →
    ∃ b > (0 : ℝ), ∀ x : A, b < ‖x‖ → x ∉ characteristicCone F δ →
      ∀ l ∈ L, ‖x + l‖ = ‖x‖ ∧ characteristicSize F (x + l) = characteristicSize F x

set_option maxHeartbeats 1400000 in
theorem largeCharacteristicCoset (d : F) (δ : ℝ) : LargeCharacteristicCosetStatement (A := A) F d δ := by
  intro hd hδ L hL
  let K := closedBall (0 : A) 1 ∩
    ({x : A | 1 / ‖d‖ ≤ ‖x‖} ∩ (characteristicCone F δ : Set A)ᶜ)
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    ((isClosed_le continuous_const continuous_norm).inter (isOpen_characteristicCone δ).isClosed_compl)
  have hPos (x : A) (hx : x ∈ K) : 0 < characteristicSize F x := by
    have hn : 0 < ‖x‖ := (one_div_pos.mpr (zero_lt_one.trans hd)).trans_le hx.2.1
    have hlower : δ * ‖x‖ ≤ (characteristicSize F x : ℝ) := not_lt.mp hx.2.2
    exact NNReal.coe_pos.mp ((mul_pos hδ hn).trans_le hlower)
  obtain ⟨ε, hε, hMove⟩ := characteristicSize_uniform_add hK hPos
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (continuous_id : Continuous (id : A → A)).continuousOn
  let b := max 1 (max B (B / ε))
  refine ⟨b, zero_lt_one.trans_le (le_max_left _ _), fun x hx hCone l hl => ?_⟩
  have hxn : 0 < ‖x‖ := (zero_lt_one.trans_le (le_max_left _ _ : (1 : ℝ) ≤ b)).trans hx
  obtain ⟨a, ha, hUpper, hLower, _⟩ := rescale_to_shell hd zero_lt_one (norm_pos_iff.mp hxn)
  have hScaled : a • x ∈ K := by
    refine ⟨?_, hLower, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact hUpper.le
    · exact fun h => hCone ((smul_mem_characteristicCone_iff δ ha x).mp h)
  have hlt : ‖l‖ < ‖x‖ := (hB l hl).trans_lt (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hx)
  have hnorm : ‖x + l‖ = ‖x‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne.symm, max_eq_left hlt.le]
  have hBE : B < ε * ‖x‖ := by
    have h := (div_lt_iff₀ hε).mp (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hx : B / ε < ‖x‖)
    simpa only [mul_comm] using h
  have hScale : ‖a • l‖ < ε := by
    rw [norm_smul]
    calc
      _ ≤ ‖a‖ * B := mul_le_mul_of_nonneg_left (hB l hl) (norm_nonneg _)
      _ < ‖a‖ * (ε * ‖x‖) := mul_lt_mul_of_pos_left hBE (norm_pos_iff.mpr ha)
      _ = ε * ‖a • x‖ := by rw [norm_smul]; ring
      _ ≤ ε := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hUpper.le hε.le
  have h := hMove (a • x) hScaled (a • l) hScale
  rw [← smul_add, characteristicSize_smul, characteristicSize_smul] at h
  exact ⟨hnorm, mul_left_cancel₀ (fun hn => ha (nnnorm_eq_zero.mp hn)) h⟩

end Langlands.HarmonicAnalysis.UnitConjugation
