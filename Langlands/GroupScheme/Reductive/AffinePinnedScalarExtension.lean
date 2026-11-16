import Langlands.GroupScheme.Reductive.AffinePinnedRootVectors
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar extension of supplied affine pinned models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u}) (A : Type u) [CommRing A] [Algebra M.ring A]

local instance : Smooth M.group.X.hom := M.reductive.smooth
local instance : IsAffineHom (M.groupOver (algebraBaseMap M.ring A)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (algebraBaseMap M.ring A)))

/-- Extend an original trivialized exponent weight line through the actual
arbitrary-ring weight-space scalar-extension equivalence. -/
def scalarWeightTrivialization (m : M.coordinates → ℤ)
    (X : M.ring ≃ₗ[M.ring]
      splitTorus.exponentWeightSpace M.coordinates M.group M.inclusion m) :
    A ≃ₗ[A] splitTorus.exponentWeightSpace M.coordinates
      (M.groupOver (algebraBaseMap M.ring A))
      (M.inclusionOver (algebraBaseMap M.ring A)) m := by
  classical
  exact (TensorProduct.AlgebraTensorModule.rid M.ring A A).symm.trans
    ((X.baseChange M.ring A _ _).trans
      (splitTorus.exponentWeightBaseChangeEquiv (K := A)
        M.group M.coordinates M.inclusion m))

/-- The new value at one is the actual scalar extension of the chosen
original Lie vector. -/
theorem scalarWeightTrivialization_one (m : M.coordinates → ℤ)
    (X : M.ring ≃ₗ[M.ring]
      splitTorus.exponentWeightSpace M.coordinates M.group M.inclusion m) :
    (M.scalarWeightTrivialization A m X 1).val =
      Lie.smoothSchemeScalarExtension (K := A) M.group (1 ⊗ₜ[M.ring] (X 1).val) := by
  classical
  simp only [scalarWeightTrivialization, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.rid_symm_apply, LinearEquiv.baseChange_tmul]
  exact splitTorus.exponentWeightBaseChangeEquiv_tmul
    (K := A) M.group M.coordinates M.inclusion m 1 (X 1)

/-- The complete supplied affine model, including its actual original
pinning vectors, after arbitrary commutative-ring scalar extension. -/
def scalarExtension : AffinePinnedModel.{u} where
  ring := A
  group := M.groupOver (algebraBaseMap M.ring A)
  reductive := M.reductive.baseChange (algebraBaseMap M.ring A)
  coordinates := M.coordinates
  inclusion := M.inclusionOver (algebraBaseMap M.ring A)
  closed := by
    let : IsClosedImmersion
        ((baseChange (algebraBaseMap M.ring A)).map M.inclusion).hom.hom.left :=
      M.closed.baseChange _
    change IsClosedImmersion
      ((splitTorus.baseChangeIso (algebraBaseMap M.ring A) M.coordinates).inv.hom.hom.left ≫
        ((baseChange (algebraBaseMap M.ring A)).map M.inclusion).hom.hom.left)
    infer_instance
  maximal := splitTorus.isFibrewiseMaximalTorus_baseChangedHom
    M.coordinates M.group M.inclusion M.maximal (algebraBaseMap M.ring A)
  rootIndex := M.rootIndex
  rootDatum := M.rootDatum
  fibrewiseRootDatum := M.fibrewiseRootDatum.baseChange_implicit
  rootLines := fun α => ⟨(M.scalarWeightTrivialization A (M.rootDatum.root α)
    (Classical.choice (M.rootLines α)).symm).symm⟩
  basis := M.basis
  pinning := fun s => M.scalarWeightTrivialization A (M.rootDatum.root s) (M.pinning s)

@[simp]
theorem scalarExtension_pinning_one (s : M.basis.support) :
    ((M.scalarExtension A).pinning s 1).val =
      Lie.smoothSchemeScalarExtension (K := A) M.group
        (1 ⊗ₜ[M.ring] (M.pinning s 1).val) :=
  M.scalarWeightTrivialization_one A (M.rootDatum.root s) (M.pinning s)

/-- The transported pinning vector projects to the coefficient extension
of the original actual dual-number vector. -/
theorem scalarExtension_pinning_fst (s : M.basis.support) :
    (((M.scalarExtension A).pinning s 1).val.toMul.val).left ≫
        pullback.fst M.group.X.hom (algebraBaseMap M.ring A) =
      (M.rootVectorAt A s).val.left := by
  rw [scalarExtension_pinning_one, Lie.smoothSchemeScalarExtension_tmul, one_smul]
  have hk := congrArg (fun X : Additive (lieKernel M.group A) => X.toMul.val.left)
    ((Lie.kernelBaseChangeLinearEquiv M.ring A M.group A).apply_symm_apply
      (lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning s 1).val))
  exact hk

/-- The scalar-extended model's chosen vector is exactly the previously
constructed actual pinning point on the coefficient test. -/
theorem scalarExtension_pinning_point (s : M.basis.support) :
    (((M.scalarExtension A).pinning s 1).val.toMul.val).left =
      M.rootVectorPoint (algebraBaseMap M.ring A) A (𝟙 _)
        (by simp only [Category.id_comp]) s := by
  apply pullback.hom_ext
  · rw [scalarExtension_pinning_fst, rootVectorPoint_fst]
  · change (((M.scalarExtension A).pinning s 1).val.toMul.val).left ≫
      (M.scalarExtension A).group.X.hom = _
    rw [Over.w]
    change algebraBaseMap A (DualNumber A) =
      M.rootVectorPoint (algebraBaseMap M.ring A) A (𝟙 _)
        (by simp only [Category.id_comp]) s ≫
          (M.groupOver (algebraBaseMap M.ring A)).X.hom
    rw [rootVectorPoint_snd, Category.comp_id]

end Langlands.GroupScheme.AffinePinnedModel
