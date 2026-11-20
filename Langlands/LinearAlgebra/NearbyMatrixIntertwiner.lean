import Langlands.LinearAlgebra.MatrixConjugationConormal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Near-identity intertwiners for nearby real matrices -/

noncomputable section

open Matrix
open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- The matrix intertwining equation is the kernel of this linear map. -/
def matrixIntertwinerMap (A B : Mat) : Mat →L[ℝ] Mat :=
  (ContinuousLinearMap.mul ℝ Mat).flip A - ContinuousLinearMap.mul ℝ Mat B

@[simp]
theorem matrixIntertwinerMap_apply (A B X : Mat) :
    matrixIntertwinerMap A B X = X * A - B * X := rfl

/-- Left multiplication by a unit intertwiner preserves the rank of the equation. -/
theorem finrank_range_matrixIntertwinerMap_of_conjugate (A B : Mat) (u : Matˣ)
    (hu : (u : Mat) * A = B * u) :
    Module.finrank ℝ (LinearMap.range (matrixIntertwinerMap A B).toLinearMap) =
      Module.finrank ℝ (LinearMap.range (matrixConjugationTangent A)) := by
  let e := u.mulLeftLinearEquiv ℝ Mat
  have he : (matrixIntertwinerMap A B).toLinearMap.comp e.toLinearMap =
      e.toLinearMap.comp (matrixConjugationTangent A) := by
    ext1 X
    change ((u : Mat) * X) * A - B * ((u : Mat) * X) = (u : Mat) * (X * A - A * X)
    rw [mul_sub, mul_assoc _ X A, ← mul_assoc B, ← hu, mul_assoc _ A X]
  have hr := congrArg LinearMap.range he
  rw [LinearEquiv.range_comp, LinearMap.range_comp] at hr
  rw [hr, e.finrank_map_eq]

/-- Close to `(C,C)`, the rank bound on the intertwining equation suffices for a smooth
near-identity solution. The correction lies in the image of the prescribed right inverse
of the commutator map onto its range at `C`. -/
theorem exists_smooth_nearbyMatrixIntertwiner (C : Mat)
    (J : (LinearMap.range (matrixConjugationTangent C)) →L[ℝ] Mat)
    (hJ : ∀ v : LinearMap.range (matrixConjugationTangent C),
      matrixConjugationTangent C (J v) = v) :
    ∃ (U : Set (Mat × Mat)) (g : Mat × Mat → Mat),
      IsOpen U ∧ (C, C) ∈ U ∧ g (C, C) = 1 ∧ ContDiffOn ℝ ∞ g U ∧
      (∀ p, g p - 1 ∈ LinearMap.range J.toLinearMap) ∧
      ∀ p ∈ U, IsUnit (g p) ∧
        (Module.finrank ℝ (LinearMap.range (matrixIntertwinerMap p.1 p.2).toLinearMap) ≤
          Module.finrank ℝ (LinearMap.range (matrixConjugationTangent C)) →
          g p * p.1 = p.2 * g p) := by
  let L := matrixConjugationTangent C
  let T := LinearMap.range L
  let _ : CompleteSpace T := FiniteDimensional.complete ℝ T
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl T
  let P : Mat →L[ℝ] T := (T.projectionOnto W hW).toContinuousLinearMap
  have hP (v : T) : P v = v := Submodule.projectionOnto_apply_left hW v
  let M (p : Mat × Mat) : T →L[ℝ] T :=
    P.comp ((matrixIntertwinerMap p.1 p.2).comp J)
  have hM : ContDiff ℝ ∞ M := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    change ContDiff ℝ ∞ fun p : Mat × Mat => P (J v * p.1 - p.2 * J v)
    exact P.contDiff.comp ((contDiff_const.mul contDiff_fst).sub (contDiff_snd.mul contDiff_const))
  have hM₀ : M (C, C) = 1 := by
    ext1 v
    change P (L (J v)) = v
    rw [hJ, hP]
  let V := M ⁻¹' {u | IsUnit u}
  have hV : IsOpen V := (Units.isOpen (R := T →L[ℝ] T)).preimage hM.continuous
  have hV₀ : (C, C) ∈ V := by
    change IsUnit (M (C, C))
    rw [hM₀]
    exact isUnit_one
  let v (p : Mat × Mat) : T := Ring.inverse (M p) (P (p.2 - p.1))
  let g (p : Mat × Mat) := 1 + J (v p)
  have hg₀ : g (C, C) = 1 := by simp [g, v]
  have hg : ContDiffOn ℝ ∞ g V := by
    intro p hp
    obtain ⟨u, hu⟩ := hp
    have hi : ContDiffAt ℝ ∞ Ring.inverse (M p) :=
      hu ▸ contDiffAt_ringInverse ℝ (R := T →L[ℝ] T) u
    have hv : ContDiffAt ℝ ∞ v p :=
      (hi.comp p hM.contDiffAt).clm_apply
        ((P.contDiff.comp (contDiff_snd.sub contDiff_fst)).contDiffAt)
    exact (contDiffAt_const.add (J.contDiff.contDiffAt.comp p hv)).contDiffWithinAt
  let U := V ∩ g ⁻¹' {u | IsUnit u}
  have hU : IsOpen U := hg.continuousOn.isOpen_inter_preimage hV Units.isOpen
  have hU₀ : (C, C) ∈ U := by
    refine ⟨hV₀, ?_⟩
    change IsUnit (g (C, C))
    rw [hg₀]
    exact isUnit_one
  refine ⟨U, g, hU, hU₀, hg₀, hg.mono Set.inter_subset_left, ?_, fun p hp => ⟨hp.2, ?_⟩⟩
  · intro p
    exact ⟨v p, by change J (v p) = 1 + J (v p) - 1; abel⟩
  intro hrank
  let Lp := (matrixIntertwinerMap p.1 p.2).toLinearMap
  let q : LinearMap.range Lp →ₗ[ℝ] T := P.toLinearMap.comp (LinearMap.range Lp).subtype
  have hMunit : IsUnit (M p) := hp.1
  have hcancel (x : T) : M p (Ring.inverse (M p) x) = x :=
    congrArg (fun E : T →L[ℝ] T => E x) (Ring.mul_inverse_cancel (M p) hMunit)
  have hq : Function.Surjective q := by
    intro x
    refine ⟨⟨Lp (J (Ring.inverse (M p) x)), ⟨_, rfl⟩⟩, ?_⟩
    exact hcancel x
  have hd : Module.finrank ℝ (LinearMap.range Lp) = Module.finrank ℝ T :=
    le_antisymm hrank (LinearMap.finrank_le_finrank_of_surjective hq)
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hq
  have hz : P (g p * p.1 - p.2 * g p) = 0 := by
    have he : g p * p.1 - p.2 * g p = (p.1 - p.2) + Lp (J (v p)) := by
      change (1 + J (v p)) * p.1 - p.2 * (1 + J (v p)) =
        (p.1 - p.2) + (J (v p) * p.1 - p.2 * J (v p))
      noncomm_ring
    rw [he, map_add, map_sub]
    change P p.1 - P p.2 + M p (v p) = 0
    rw [show M p (v p) = P (p.2 - p.1) from hcancel _, map_sub]
    abel
  let w : LinearMap.range Lp := ⟨Lp (g p), ⟨g p, rfl⟩⟩
  have hw : q w = q 0 := by
    rw [map_zero]
    exact hz
  exact sub_eq_zero.mp (congrArg Subtype.val (hi hw))

end Langlands
