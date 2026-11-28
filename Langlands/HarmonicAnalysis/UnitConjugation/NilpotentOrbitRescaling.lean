import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentApproximation
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitProjection
import Mathlib.Topology.MetricSpace.Thickening

/-! # Transferring a nilpotent-annulus estimate across a compact orbit -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Metric _root_.Topology

variable {F A : Type*} [NontriviallyNormedField F] [NormedRing A]

/-- The nilpotent points of the closed norm annulus used to normalize frequencies. -/
def nilpotentAnnulus (d : F) (A : Type*) [NormedRing A] : Set A :=
  {x | 1 / ‖d‖ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ IsNilpotent x}

/-- A small neighborhood of the nilpotent annulus permits transfer of a rescaling
from a large orbit frequency to its original representative. -/
def NilpotentOrbitRescalingStatement (d : F) (V : Set A) [IsUltrametricDist A]
    [CompleteSpace F] [NormedAlgebra F A] [FiniteDimensional F A] [ProperSpace A] : Prop :=
  IsOpen V → nilpotentAnnulus d A ⊆ V →
  ∃ W : Set A, IsOpen W ∧ nilpotentAnnulus d A ⊆ W ∧
    ∀ (K : Subgroup Aˣ) (L : AddSubgroup A) (b : ℝ), IsCompact (L : Set A) → 0 < b →
      (∀ k ∈ K, ∀ x : A, ‖conjugationHomeomorph k x‖ = ‖x‖) →
      ∃ t > (0 : ℝ), ∀ x y : A, t < ‖x‖ → y ∈ conjugationCosetOrbit K L x →
        b < ‖y‖ ∧ ((∃ a : F, a ≠ 0 ∧ ‖a • y‖ ≤ 1 ∧ a • y ∈ W) → ∃ a : F, a ≠ 0 ∧ a • x ∈ V)

variable [IsUltrametricDist A] [CompleteSpace F] [NormedAlgebra F A] [FiniteDimensional F A] [ProperSpace A]

set_option maxHeartbeats 1000000 in
theorem nilpotentOrbitRescaling (d : F) (V : Set A) : NilpotentOrbitRescalingStatement d V := by
  intro hV hNV
  let N := nilpotentAnnulus d A
  have hNilClosed : IsClosed {x : A | IsNilpotent x} := by
    have hset : {x : A | IsNilpotent x} = leftRegularCoefficients F ⁻¹' {0} := by
      ext x
      exact (leftRegularCoefficients_eq_zero_iff x).symm
    rw [hset]
    exact isClosed_singleton.preimage continuous_leftRegularCoefficients
  have hN : IsCompact N := by
    have hset : N = closedBall 0 1 ∩ ({x | 1 / ‖d‖ ≤ ‖x‖} ∩ {x | IsNilpotent x}) := by
      ext x
      simp only [N, nilpotentAnnulus, mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_zero_right]
      tauto
    rw [hset]
    exact (isCompact_closedBall _ _).inter_right ((isClosed_le continuous_const continuous_norm).inter hNilClosed)
  obtain ⟨ε, hε, hTV⟩ := hN.exists_thickening_subset_open hV hNV
  let W := thickening ε N
  refine ⟨W, isOpen_thickening, self_subset_thickening hε N, ?_⟩
  intro K L b hL hb hIsom
  obtain ⟨D, hD⟩ := hL.exists_bound_of_continuousOn (continuous_id : Continuous (id : A → A)).continuousOn
  let t := max b (max D (D / ε))
  have ht : 0 < t := hb.trans_le (le_max_left _ _)
  refine ⟨t, ht, ?_⟩
  intro x y hx hy
  obtain ⟨k, hk, l, hl, rfl⟩ := hy
  let z := conjugationHomeomorph k x + l
  have hDx : D < ‖x‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hx
  have hDε : D < ε * ‖x‖ := by
    have h := (div_lt_iff₀ hε).mp (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hx : D / ε < ‖x‖)
    simpa only [mul_comm] using h
  have hlt : ‖l‖ < ‖conjugationHomeomorph k x‖ := by
    rw [hIsom k hk]
    exact (hD l hl).trans_lt hDx
  have hzn : ‖z‖ = ‖x‖ := by
    rw [show z = conjugationHomeomorph k x + l from rfl,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne.symm, max_eq_left hlt.le, hIsom k hk]
  refine ⟨hzn ▸ (le_max_left _ _).trans_lt hx, ?_⟩
  rintro ⟨a, ha, hNorm, haz⟩
  have haD : ‖a‖ * D < ε := calc
    _ < ‖a‖ * (ε * ‖x‖) := mul_lt_mul_of_pos_left hDε (norm_pos_iff.mpr ha)
    _ = ε * ‖a • z‖ := by rw [norm_smul, hzn]; ring
    _ ≤ ε := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hNorm hε.le
  let C := conjugationHomeomorph k⁻¹
  have hcNorm (u : A) : ‖C u‖ = ‖u‖ := hIsom _ (K.inv_mem hk) u
  have hcAdd (u v : A) : C (u + v) = C u + C v := by
    change conjugationHomeomorph k⁻¹ (u + v) = _
    simp only [C, conjugationHomeomorph_apply, mul_add, add_mul]
  have hcSub (u v : A) : C (u - v) = C u - C v := by
    simp only [C, conjugationHomeomorph_apply, mul_sub, sub_mul]
  have hcSmul (u : A) : C (a • u) = a • C u := by
    simp only [C, conjugationHomeomorph_apply, mul_smul_comm, smul_mul_assoc]
  have hcX : C (conjugationHomeomorph k x) = x := by
    change conjugationHomeomorph k⁻¹ (conjugationHomeomorph k x) = x
    rw [← conjugationHomeomorph_mul, inv_mul_cancel, conjugationHomeomorph_one]
  obtain ⟨n, hn, hnNear⟩ := mem_thickening_iff.mp haz
  have hnC : C n ∈ N := by
    refine ⟨(hcNorm n).symm ▸ hn.1, (hcNorm n).symm ▸ hn.2.1, ?_⟩
    apply (leftRegularCoefficients_eq_zero_iff (F := F) (C n)).mp
    rw [show C n = conjugationHomeomorph k⁻¹ n from rfl, leftRegularCoefficients_conjugation]
    exact (leftRegularCoefficients_eq_zero_iff n).mpr hn.2.2
  have hErr : ‖C (a • z) - a • x‖ < ε := by
    rw [hcSmul, show C z = x + C l from (hcAdd _ _).trans (by rw [hcX]),
      smul_add, add_sub_cancel_left, norm_smul, hcNorm]
    exact (mul_le_mul_of_nonneg_left (hD l hl) (norm_nonneg _)).trans_lt haD
  have hNear : ‖C (a • z) - C n‖ < ε := by
    rw [← hcSub, hcNorm, ← dist_eq_norm]
    exact hnNear
  refine ⟨a, ha, hTV (mem_thickening_iff.mpr ⟨C n, hnC, ?_⟩)⟩
  rw [dist_eq_norm, show a • x - C n = (a • x - C (a • z)) + (C (a • z) - C n) by abel]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    (max_lt ((norm_sub_rev _ _).trans_lt hErr) hNear)

end Langlands.HarmonicAnalysis.UnitConjugation
