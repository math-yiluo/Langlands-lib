import Langlands.GroupScheme.Reductive.SpecialLinearRoots
import Langlands.GroupScheme.Lie.AffineBracketMatrix
import Langlands.GroupScheme.Lie.FieldAlgebraLie

/-! # Normalized brackets of opposite root vectors in `SL₂` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Langlands.GroupScheme.Lie.FieldLie

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k]

local notation "Base" => CommRingCat.of k
local notation "SL" => SpecialLinear.groupScheme (Fin 2) Base
local notation "D" => splitTorus.commGroupScheme (Spec Base) (ULift (Fin 1))
local notation "d" => diagonalTorus 1 Base
local notation "L" => Additive (lieKernel SL k)

/-- The matrix differential of `SL₂` carries the tangent Lie bracket
to the matrix commutator. -/
def lieMatrixLieHom : L →ₗ⁅k⁆ Matrix (Fin 2) (Fin 2) k :=
  GeneralLinear.DualNumber.pointKernelLieEquiv.symm.toLieHom.comp
    (Lie.targetMapLieHom (inclusion (Fin 2) Base) k)

@[simp] theorem lieMatrixLieHom_apply (x : L) : lieMatrixLieHom x = lieMatrix x :=
  rfl

private theorem mem_weightSpace_of_lieMatrix_single
    {root : characterLattice D} {p q : Fin 2}
    (hroot : GeneralLinear.characterCoordEquiv (Fin 1) k root =
      weightCoord 1 p - weightCoord 1 q)
    {x : L} (hx : lieMatrix x = Matrix.single p q 1) :
    x ∈ weightSpace d root := by
  rw [mem_weightSpace_diagonalTorus_iff_support, hx, hroot]
  intro i j hij
  obtain ⟨rfl, rfl⟩ : p = i ∧ q = j := by
    by_contra h
    exact hij (Matrix.single_apply_of_ne _ _ _ _ _ h)
  rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
set_option synthInstance.maxHeartbeats 100000 in
/-- In `SL₂`, for every root there are opposite root vectors `e` and `f`
with `e ≠ 0` and `[[e, f], e] = 2e`. -/
theorem exists_normalizedRootVectors {root : characterLattice D}
    (hroot : root ∈ roots d) :
    ∃ e ∈ weightSpace d root, ∃ f ∈ weightSpace d (-root),
      e ≠ (0 : L) ∧ ⁅⁅e, f⁆, e⁆ = (2 : k) • e := by
  obtain ⟨p, q, hpq, hcoord⟩ := exists_coord_of_mem_roots hroot
  obtain ⟨e, he⟩ := exists_lieMatrix_eq (R := Base) _
    (Matrix.trace_single_eq_of_ne p q (1 : k) hpq)
  obtain ⟨f, hf⟩ := exists_lieMatrix_eq (R := Base) _
    (Matrix.trace_single_eq_of_ne q p (1 : k) hpq.symm)
  have hneg : GeneralLinear.characterCoordEquiv (Fin 1) k (-root) =
      weightCoord 1 q - weightCoord 1 p := by
    rw [map_neg, hcoord, neg_sub]
  refine ⟨e, mem_weightSpace_of_lieMatrix_single hcoord he, f,
    mem_weightSpace_of_lieMatrix_single hneg hf, ?_, ?_⟩
  · intro h
    have hentry := congrArg (fun x : L => lieMatrix x p q) h
    apply one_ne_zero (α := k)
    simpa only [he, map_zero, Matrix.single_apply_same, Matrix.zero_apply] using hentry
  · apply lieMatrix_injective (R := Base) (A := k)
    change lieMatrixLieHom ⁅⁅e, f⁆, e⁆ = lieMatrixLieHom ((2 : k) • e)
    simp only [LieHom.map_lie, map_smul, lieMatrixLieHom_apply, he, hf, Ring.lie_def]
    simp only [Matrix.single_mul_single_same, one_mul, sub_mul, mul_sub, two_smul]
    rw [Matrix.single_mul_single_of_ne (1 : k) q q p hpq.symm 1,
      Matrix.single_mul_single_of_ne (1 : k) p q p hpq.symm 1,
      sub_zero, zero_sub, sub_neg_eq_add]

end Langlands.GroupScheme.SpecialLinear.FinSucc
