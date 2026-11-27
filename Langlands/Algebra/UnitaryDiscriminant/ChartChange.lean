import Langlands.Algebra.UnitaryDiscriminant.Class

/-! # Change of matrix coordinates in the unitary discriminant -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

open BrauerComparison LinearAlgebra.UnitaryTwistedDescent
open ScalarTwoCocycle (coboundary)
open Matrix.GeneralLinearGroup (det)

section MatrixCoordinates

variable {F M : Type u} [Field F] [Field M] [Algebra F M]
  {I : Type} [Fintype I] [DecidableEq I]
  {H : Subgroup (M ≃ₐ[F] M)}

/-- Transport the twisted lifts through conjugation by the coordinate matrix `T`. -/
def conjugatedLift (T : GL I M) (P : Gal(M/F) → GL I M) (g : Gal(M/F)) : GL I M :=
  T * P g * (twistGL H g T)⁻¹

private theorem twistedAct_conjugatedLift (T : GL I M) (P : Gal(M/F) → GL I M)
    (g : Gal(M/F)) (X : Matrix I I M) :
    twistedAct H (conjugatedLift (H := H) T P) g
        ((T : Matrix I I M) * X * (T⁻¹ : GL I M)) =
      (T : Matrix I I M) * twistedAct H P g X * (T⁻¹ : GL I M) := by
  rw [twistedAct_eq, twistedAct_eq, coeffTwist_conj]
  simp only [conjugatedLift, Units.val_mul, _root_.mul_inv_rev, inv_inv, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

private theorem conjugatedLift_mul
    (hmul : ∀ g h : Gal(M/F), g * h ∈ H ↔ (g ∈ H ↔ h ∈ H))
    (T : GL I M) (P : Gal(M/F) → GL I M) (c : Gal(M/F) → Gal(M/F) → Mˣ)
    (hc : ∀ g h, P g * twistGL H g (P h) =
      GeneralLinearGroup.scalar I (c g h) * P (g * h))
    (g h : Gal(M/F)) :
    conjugatedLift (H := H) T P g * twistGL H g (conjugatedLift (H := H) T P h) =
      GeneralLinearGroup.scalar I (c g h) * conjugatedLift (H := H) T P (g * h) := by
  simp only [conjugatedLift, twistGL_mul, twistGL_inv, twistGL_twistGL hmul]
  calc
    _ = T * (P g * twistGL H g (P h)) * (twistGL H (g * h) T)⁻¹ := by group
    _ = _ := by
      rw [hc, ← mul_assoc T, ← GeneralLinearGroup.scalar_commute (c g h) T]
      simp only [mul_assoc]

open Classical in
/-- Conjugating the chart lifts multiplies the determinant factor set by the coboundary of
`g ↦ g(det T)` on the outer coset and `g ↦ 1` on the center-fixing subgroup. -/
theorem detCocycle_conjugatedLift
    (hmul : ∀ g h : Gal(M/F), g * h ∈ H ↔ (g ∈ H ↔ h ∈ H))
    (T : GL I M) (P : Gal(M/F) → GL I M) (c : Gal(M/F) → Gal(M/F) → Mˣ) (m : ℕ)
    (g h : Gal(M/F)) :
    detCocycle H (conjugatedLift (H := H) T P) c m g h =
      coboundary (fun (s : Gal(M/F)) => if s ∈ H then 1 else s • det T) g h *
        detCocycle H P c m g h := by
  classical
  by_cases hg : g ∈ H <;> by_cases hh : h ∈ H
  · have hgh : g * h ∈ H := (hmul g h).2 (iff_of_true hg hh)
    simp [detCocycle, coboundary, hg, hh, hgh]
  · have hgh : g * h ∉ H := by simp [hmul, hg, hh]
    simp [detCocycle, coboundary, hg, hh, hgh, mul_smul]
  · have hgh : g * h ∉ H := by simp [hmul, hg, hh]
    rw [detCocycle_of_not_mem_of_mem _ _ _ hg hh, detCocycle_of_not_mem_of_mem _ _ _ hg hh]
    simp only [coboundary, ite_eq_right hg, ite_eq_left hh, ite_eq_right hgh, smul_one, mul_one,
      conjugatedLift, map_mul, map_inv, det_twistGL, twistUnit_of_mem hh, smul_mul',
      smul_inv', ← mul_smul]
    simp only [mul_assoc, mul_left_comm, mul_comm]
  · have hgh : g * h ∈ H := by simp [hmul, hg, hh]
    rw [detCocycle_of_not_mem_of_not_mem _ _ _ hg hh, detCocycle_of_not_mem_of_not_mem _ _ _ hg hh]
    simp only [coboundary, ite_eq_right hg, ite_eq_right hh, ite_eq_left hgh, inv_one, mul_one,
      conjugatedLift, map_mul, map_inv, det_twistGL, twistUnit_of_not_mem hh, inv_inv, smul_mul']
    simp only [mul_assoc, mul_left_comm, mul_comm]

end MatrixCoordinates

section SplittingChart

variable {F L M : Type u} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
  [Algebra L M] [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L]
  {B : Type v} [Ring B] [Algebra L B] {m : ℕ}
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) {τ : B → B} (hτ : IsUnitaryInvolution ι τ)

/-- The relative discriminant class is independent of the matrix chart over one splitting field. -/
theorem relativeDiscriminantClass_eq_of_chart
    (e f : M ⊗[L] B ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M) :
    relativeDiscriminantClass hι hτ e = relativeDiscriminantClass hι hτ f := by
  classical
  let H := centerFixing F L M
  let P := chartLift hι hτ e
  let c := chartFactor hι hτ e
  obtain ⟨T, hT⟩ := MatrixAlgebra.exists_unit_conj_of_algEquiv (e.symm.trans f)
  have hchart (b : B) : chartMap f b =
      (T : Matrix (Fin (2 * m)) (Fin (2 * m)) M) * chartMap e b * (T⁻¹ : GL (Fin (2 * m)) M) := by
    simpa only [chartMap_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] using hT (chartMap e b)
  let Q := conjugatedLift (H := H) T P
  have hm := mul_mem_centerFixing_iff (M := M) hι
  have hc := conjugatedLift_mul hm T P c (chartLift_mul hι hτ e)
  have hq := detCocycle_isTwoCocycle_of_lifts hm Q c hc m (Fintype.card_fin _)
  have hinner (g : Gal(M/F)) (hg : g ∈ H) (b : B) :
      twistedAct H Q g (chartMap f b) = chartMap f b := by
    rw [hchart, twistedAct_conjugatedLift, twistedAct_chartLift_of_mem hι hτ e hg, ← hchart]
  have houter (g : Gal(M/F)) (hg : g ∉ H) (b : B) :
      twistedAct H Q g (chartMap f b) = chartMap f (τ b) := by
    rw [hchart, twistedAct_conjugatedLift, twistedAct_chartLift_of_not_mem hι hτ e hg, ← hchart]
  calc
    relativeDiscriminantClass hι hτ e = unitClass (detCocycle H Q c m) hq :=
      (unitClass_eq_of_coboundary_mul hq (discriminantCocycle_isTwoCocycle hι hτ e) _
        (detCocycle_conjugatedLift hm T P c m)).symm
    _ = relativeDiscriminantClass hι hτ f :=
      relativeDiscriminantClass_eq_of_lifts hι hτ f Q c hinner houter hc

end SplittingChart

end Langlands.UnitaryDiscriminant
