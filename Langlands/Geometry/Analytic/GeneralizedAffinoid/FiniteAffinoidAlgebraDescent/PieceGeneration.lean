import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatching
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Generation of pieces by images of local generators -/

noncomputable section

universe u

open Function Filter Topology
open scoped TensorProduct NNReal

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- The images of norm-controlled generators of a finite Banach map generate the
right leg of the affinoid pushout, with norm control. This is the argument of the
Library's `rightMap_isFiniteBanach`, with the generators made explicit. -/
theorem rightMap_coefficientMap_leftMap {n : ℕ} (b : Fin n → B) {M : ℝ} (hM : 0 < M)
    (hb : ∀ y : B, ∃ a : Fin n → A, f.coefficientMap b a = y ∧ ‖a‖ ≤ M * ‖y‖) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : algebra f g, ∃ c : Fin n → C,
      (rightMap f g).coefficientMap (fun j => leftMap f g (b j)) c = z ∧ ‖c‖ ≤ D * ‖z‖ := by
  classical
  obtain ⟨N, hN, hg⟩ := g.bounded
  obtain ⟨H, hH, hlift⟩ :=
    (tensorMap f g).isAdmissibleEpi_iff_normControlledLifts.mp
      (tensorMap_isAdmissibleEpi f g)
  obtain ⟨P, hP, hbound⟩ := (tensorMap f g).bounded
  let d : Fin n → algebra f g := fun j => leftMap f g (b j)
  have happrox : ∀ z : algebra f g, ∃ c : Fin n → C,
      dist ((rightMap f g).coefficientMap d c) z ≤ 1 / 2 * ‖z‖ ∧
      ‖c‖ ≤ ((N * M) * (H + 1)) * ‖z‖ := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact ⟨0, by simp, by simp⟩
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨y, hy, hyn⟩ := hlift z
    let ε : ℝ := ‖z‖ / (2 * (P + 1))
    have hden : 0 < 2 * (P + 1) := by positivity
    have hε : 0 < ε := div_pos hzpos hden
    have hεz : ε ≤ ‖z‖ := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg hP.le (norm_nonneg z)]
    obtain ⟨t, ht⟩ :=
      (CompletedTensorAlgebra.denseRange_toCompletion K B C).exists_dist_lt y hε
    rw [dist_eq_norm] at ht
    have htn : ‖t‖ < (H + 1) * ‖z‖ := by
      calc
        ‖t‖ = ‖CompletedTensorAlgebra.toCompletion K B C t‖ :=
          (UniformSpace.Completion.norm_coe t).symm
        _ ≤ ‖y‖ + ‖y - CompletedTensorAlgebra.toCompletion K B C t‖ := by
          simpa only [sub_sub_cancel] using
            norm_sub_le y (y - CompletedTensorAlgebra.toCompletion K B C t)
        _ < H * ‖z‖ + ε := add_lt_add_of_le_of_lt hyn ht
        _ ≤ (H + 1) * ‖z‖ := by nlinarith [hεz]
    let R : ℝ≥0 := ⟨(H + 1) * ‖z‖, by positivity⟩
    have hseminorm : UltrametricTensorSeminorm.seminormFun
        (t : B ⊗[K] C) < R := by
      exact_mod_cast htn
    let : Nonempty (UltrametricTensorSeminorm.Representation K B C t) :=
      UltrametricTensorSeminorm.Representation.nonempty (t : B ⊗[K] C)
    obtain ⟨r, hr⟩ := exists_lt_of_ciInf_lt
      (f := fun r : UltrametricTensorSeminorm.Representation K B C t => r.value)
      hseminorm
    obtain ⟨c, hc, hcn⟩ :=
      exists_coefficient_lift_representation f g b hM hN hb hg t r
    refine ⟨c, ?_, ?_⟩
    · have hceq : (rightMap f g).coefficientMap d c =
          tensorMap f g (CompletedTensorAlgebra.toCompletion K B C t) :=
        hc.trans (CompletedTensorAlgebra.lift_toCompletion _ _ t).symm
      rw [hceq]
      calc
        dist (tensorMap f g (CompletedTensorAlgebra.toCompletion K B C t)) z =
            ‖tensorMap f g (CompletedTensorAlgebra.toCompletion K B C t - y)‖ := by
          rw [map_sub, hy, dist_eq_norm]
        _ ≤ P * ‖CompletedTensorAlgebra.toCompletion K B C t - y‖ := hbound _
        _ ≤ P * ε := mul_le_mul_of_nonneg_left (by
          simpa only [norm_sub_rev] using ht.le) hP.le
        _ ≤ 1 / 2 * ‖z‖ := by
          dsimp [ε]
          rw [← mul_div_assoc]
          apply (div_le_iff₀ hden).2
          nlinarith [norm_nonneg z]
    · calc
        ‖c‖ ≤ (N * M) * (r.value : ℝ) := hcn
        _ ≤ (N * M) * ((H + 1) * ‖z‖) := mul_le_mul_of_nonneg_left
          (by exact_mod_cast hr.le) (mul_pos hN hM).le
        _ = ((N * M) * (H + 1)) * ‖z‖ := (mul_assoc _ _ _).symm
  obtain ⟨D, hD, hcoeff⟩ := exists_normControlledLifts_of_approx
    ((rightMap f g).coefficientMap d) (by positivity) happrox
  exact ⟨D, hD, hcoeff⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
