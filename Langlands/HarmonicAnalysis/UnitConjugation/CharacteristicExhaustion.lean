import Langlands.HarmonicAnalysis.UnitConjugation.CharacteristicCutoffs
import Langlands.HarmonicAnalysis.UnitConjugation.HoweRestriction

/-! # Invariant clopen exhaustion by characteristic size -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Metric Filter Function _root_.Topology
open scoped NNReal

variable {F A : Type*} [NontriviallyNormedField F] [NormedRing A] [NormedAlgebra F A]
  [FiniteDimensional F A] [CompleteSpace F] [IsUltrametricDist F]

/-- The sublevel sets used as invariant cutoffs of a distribution. -/
def characteristicSublevel (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F A]
    [FiniteDimensional F A] (n : ℕ) : Set A :=
  {x | (characteristicSize F x : ℝ) ≤ (n : ℝ) + 1}

omit [IsUltrametricDist F] in
private theorem continuous_realSize : Continuous (fun x : A => (characteristicSize F x : ℝ)) :=
  continuous_subtype_val.comp continuous_characteristicSize

private theorem isClopen_characteristicSublevel (n : ℕ) : IsClopen (characteristicSublevel (A := A) F n) := by
  refine ⟨isClosed_le (continuous_realSize (A := A) (F := F)) continuous_const, ?_⟩
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases h0 : characteristicSize F x = 0
  · have hOpen : IsOpen {y : A | (characteristicSize F y : ℝ) < (n : ℝ) + 1} :=
      isOpen_lt continuous_realSize continuous_const
    exact mem_of_superset (hOpen.mem_nhds (show (characteristicSize F x : ℝ) < (n : ℝ) + 1 by
      rw [h0, NNReal.coe_zero]; positivity)) fun y hy =>
      (show (characteristicSize F y : ℝ) < (n : ℝ) + 1 from hy).le
  · filter_upwards [(characteristicSize_spec (F := F) (A := A)).2 x (pos_iff_ne_zero.mpr h0)] with y hy
    change (characteristicSize F y : ℝ) ≤ _
    rw [hy]
    exact hx

omit [IsUltrametricDist F] in
private theorem eventually_subset_characteristicSublevel {K : Set A} (hK : IsCompact K) :
    ∀ᶠ n in atTop, K ⊆ characteristicSublevel (A := A) F n := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_realSize (A := A) (F := F)).continuousOn
  obtain ⟨m, hm⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop m] with n hn
  intro x hx
  have hle : (characteristicSize F x : ℝ) ≤ B := by
    have h := hB x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] at h
  exact hle.trans ((hm.le.trans (by exact_mod_cast hn : (m : ℝ) ≤ n)).trans (le_add_of_nonneg_right zero_le_one))

omit [CompleteSpace F] [IsUltrametricDist F] in
private theorem characteristicSublevel_compact_saturation
    (hUnit : ∃ ω : Set A, IsCompact ω ∧ {x | characteristicSize F x ≤ 1} ⊆ conjugationSaturation ω)
    (n : ℕ) : ∃ ω : Set A, IsCompact ω ∧ characteristicSublevel F n ⊆ closure (conjugationSaturation ω) := by
  obtain ⟨K, hK, hSmall⟩ := hUnit
  have hR : 0 < (n : ℝ) + 1 := by positivity
  obtain ⟨a, ha, haR⟩ := NormedField.exists_norm_lt F (one_div_pos.mpr hR)
  have ha₀ : a ≠ 0 := norm_pos_iff.mp ha
  refine ⟨(fun x : A => a⁻¹ • x) '' K, hK.image (continuous_id.const_smul a⁻¹), fun x hx => subset_closure ?_⟩
  have hBound : characteristicSize F (a • x) ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_one, characteristicSize_smul, NNReal.coe_mul, coe_nnnorm]
    have haN := (lt_div_iff₀ hR).mp haR
    exact ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans haN.le)
  obtain ⟨g, y, hy, hgy⟩ := mem_conjugationSaturation_iff.mp (hSmall hBound)
  refine mem_conjugationSaturation_iff.mpr ⟨g, a⁻¹ • y, ⟨y, hy, rfl⟩, ?_⟩
  rw [mul_smul_comm, smul_mul_assoc, hgy, smul_smul, inv_mul_cancel₀ ha₀, one_smul]

variable [ProperSpace A] [IsUltrametricDist A]

/-- The characteristic sublevels give the cutoff argument once finite dimensionality
of the vanishing restrictions and compact saturation of the unit sublevel are supplied. -/
def CharacteristicExhaustionStatement (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F A]
    [FiniteDimensional F A] (d : F) (δ : ℝ) : Prop :=
  (∃ ω : Set A, IsCompact ω ∧ {x | characteristicSize F x ≤ 1} ⊆ conjugationSaturation ω) →
  1 < ‖d‖ → 0 < δ → ∀ (L : AddSubgroup A) (hLo : IsOpen (L : Set A)) (hLc : IsCompact (L : Set A)),
    ∃ b > (0 : ℝ), ∀ (t : ℝ), b ≤ t →
      let B := {x : A | t < ‖x‖ ∧ x ∉ characteristicCone F δ}
      FiniteDimensional ℂ ((vanishingOnLatticeCosets L hLo hLc B).map (restrictToLatticeTests L)) →
      ∀ T ∈ vanishingOnLatticeCosets L hLo hLc B,
        ∃ (ω : Set A) (T' : Distribution A), IsCompact ω ∧ T' ∈ invariantSupportedIn ω ∧
          restrictToLatticeTests L T' = restrictToLatticeTests L T

set_option maxHeartbeats 1600000 in
theorem characteristicExhaustion (d : F) (δ : ℝ) : CharacteristicExhaustionStatement (A := A) F d δ := by
  intro hUnit hd hδ L hLo hLc
  obtain ⟨b, hb, hConst⟩ := largeCharacteristicCoset (A := A) d δ hd hδ L hLc
  refine ⟨b, hb, fun t ht hFin => ?_⟩
  let B := {x : A | t < ‖x‖ ∧ x ∉ characteristicCone F δ}
  have hInv (n : ℕ) (u : Aˣ) (x : A) : x ∈ characteristicSublevel F n ↔
      conjugationHomeomorph u x ∈ characteristicSublevel F n := by
    change (characteristicSize F x : ℝ) ≤ _ ↔ (characteristicSize F (conjugationHomeomorph u x) : ℝ) ≤ _
    rw [characteristicSize_conjugation]
  have hCoset : ∀ n x, x ∈ B → ∀ y ∈ Homeomorph.addLeft x '' (L : Set A),
      y ∈ characteristicSublevel F n ↔ x ∈ characteristicSublevel F n := by
    rintro n x ⟨hx, hxC⟩ _ ⟨l, hl, rfl⟩
    have hEq := (hConst x (ht.trans_lt hx) hxC l hl).2
    change (characteristicSize F (x + l) : ℝ) ≤ _ ↔ _
    rw [hEq]
    rfl
  exact howeRestrictionFromCutoffs L hLo hLc B hFin (characteristicSublevel F)
    isClopen_characteristicSublevel hInv (characteristicSublevel_compact_saturation hUnit)
    (fun _ hK => eventually_subset_characteristicSublevel hK) hCoset

end Langlands.HarmonicAnalysis.UnitConjugation
