import Langlands.GroupScheme.Lie.AdjointDifferentialBaseChange
import Langlands.GroupScheme.Lie.AdjointTangentBracket
import Langlands.GroupScheme.Lie.FieldAlgebraLie
import Langlands.GroupScheme.Lie.TorusCentralizerSliceBaseChange

/-! # Lie brackets under field extension of the base scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Langlands.GroupScheme.Lie.FieldLie Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Lie

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

private local instance : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  infer_instance

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine (G_K).X.left := isAffine_of_isAffineHom (G_K).X.hom

local instance : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (Limits.pullback.snd G.X.hom b)
  infer_instance

set_option maxRecDepth 4096 in
/-- The actual Lie-kernel comparison for a field extension preserves brackets. -/
theorem kernelBaseChangeLinearEquiv_lie (x y : Additive (lieKernel G_K K)) :
    kernelBaseChangeLinearEquiv k K G K ⁅x, y⁆ =
      ⁅kernelBaseChangeLinearEquiv k K G K x, kernelBaseChangeLinearEquiv k K G K y⁆ := by
  let c := finiteCoordinates G
  let e := kernelBaseChangeLinearEquiv k K G K
  have hcoord (z : Additive (lieKernel G_K K)) :
      coordinateEquiv (c.baseChange k K) K z = coordinateEquiv c K (e z) :=
    c.baseChange_equiv_apply z
  have hmatrix : (adjointRepresentation (c.baseChange k K)).kernelDifferential K x =
      (adjointRepresentation c).kernelDifferential K (e x) := by
    rw [MatrixRepresentation.kernelDifferential_apply, MatrixRepresentation.kernelDifferential_apply]
    change (adjointRepresentation (c.baseChange k K)).tangentMatrix K x.toMul =
      (adjointRepresentation c).tangentMatrix K (e (Additive.ofMul x.toMul)).toMul
    rw [show e (Additive.ofMul x.toMul) = Additive.ofMul (kernelBaseChangeEquiv k K G K x.toMul)
      from kernelBaseChangeLinearEquiv_ofMul x.toMul]
    exact adjointRepresentation_baseChange_tangentMatrix c x.toMul
  apply (coordinateEquiv c K).injective
  change coordinateEquiv c K (e ⁅x, y⁆) = coordinateEquiv c K ⁅e x, e y⁆
  calc
    _ = coordinateEquiv (c.baseChange k K) K ⁅x, y⁆ := (hcoord _).symm
    _ = (adjointRepresentation (c.baseChange k K)).kernelDifferential K x *ᵥ
        coordinateEquiv (c.baseChange k K) K y :=
      (adjointKernelDifferential_mulVec (c.baseChange k K) K x y).symm
    _ = (adjointRepresentation c).kernelDifferential K (e x) *ᵥ coordinateEquiv c K (e y) := by
      rw [hmatrix, hcoord]
    _ = _ := adjointKernelDifferential_mulVec c K (e x) (e y)

/-- The linear Lie-kernel comparison under field extension, as a Lie equivalence. -/
def kernelBaseChangeLieEquiv :
    Additive (lieKernel G_K K) ≃ₗ⁅K⁆ Additive (lieKernel G K) :=
  { kernelBaseChangeLinearEquiv k K G K with
    map_lie' := fun {x y} => kernelBaseChangeLinearEquiv_lie k K G x y }

@[simp]
theorem kernelBaseChangeLieEquiv_toLinearEquiv :
    (kernelBaseChangeLieEquiv k K G).toLinearEquiv = kernelBaseChangeLinearEquiv k K G K := rfl

end Langlands.GroupScheme.Lie
