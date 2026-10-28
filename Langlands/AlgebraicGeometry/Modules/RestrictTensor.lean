import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensor
import Langlands.AlgebraicGeometry.Modules.TensorMonoidal

/-! # The open-restriction comparison for the sheaf tensor product

For an open subscheme `U ⊆ X` and module sheaves `M`, `N` on `X`, this file constructs the
canonical comparison morphism `M|_U ⊗ N|_U ⟶ (M ⊗ N)|_U`. Its invertibility and its value on
pure tensors of sections belong to the separate `RestrictTensorStatement` successor.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.Scheme.Modules

open TopologicalSpace Opposite

variable {X : Scheme.{u}} (U : X.Opens)

/-- The ring map along which `Scheme.Modules.restrictFunctor U.ι` restricts scalars. -/
abbrev restrictRingMap :
    U.toScheme.ringCatSheaf.obj ⟶ U.ι.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
  Functor.whiskerRight
    ({ app V := (U.ι.appIso V.unop).inv } : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf)
    (forget₂ CommRingCat RingCat)

/-- The sectionwise comparison `M(ιV) ⊗_{𝒪_U(V)} N(ιV) → M(ιV) ⊗_{𝒪_X(ιV)} N(ιV)`. -/
def restrictTensorLift (M N : X.Modules) :
    (M.restrict U.ι).val ⊗ (N.restrict U.ι).val ⟶
      (PresheafOfModules.pushforward (restrictRingMap U)).obj (M.val ⊗ N.val) where
  app V := restrictScalarsTensorLift (U.ι.appIso V.unop).inv.hom
    (𝟙 ((M.val ⊗ N.val).obj (op (U.ι ''ᵁ V.unop))))
  naturality := by
    intro V W i
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    rfl

/-- The presheaf map from the tensor of restrictions to the restricted sheaf tensor. -/
def restrictTensorPresheafHom (M N : X.Modules) :
    (M.restrict U.ι).val ⊗ (N.restrict U.ι).val ⟶ ((tensorObj M N).restrict U.ι).val :=
  restrictTensorLift U M N ≫
    (PresheafOfModules.pushforward (restrictRingMap U)).map (tensorSheafifyUnit M N)

/-- The comparison from the tensor of restrictions to the restriction of the tensor. -/
def restrictTensorHom (M N : X.Modules) :
    tensorObj (M.restrict U.ι) (N.restrict U.ι) ⟶ (tensorObj M N).restrict U.ι :=
  (tensorHomEquiv _ _ _).symm (restrictTensorPresheafHom U M N)

end Langlands.Scheme.Modules
