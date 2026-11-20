import Langlands.Automorphic.CuspidalPresentationTensorDecomposition
import Langlands.Automorphic.PadicLocalCategory
import Langlands.Global.FiniteAdelicGL.LocalTensorSeparation

/-! The actual local factor with its multiplicity on the whole cuspidal carrier. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open _root_.Representation
open scoped TensorProduct

universe u

namespace Langlands

namespace Automorphic.CuspidalSpectralPresentation

open Global Global.FiniteAdelicGL

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r} (P : CuspidalSpectralPresentation.{u, u} T)

attribute [local instance] presentationTensorRationalGroup presentationTensorContinuousGroup
  presentationTensorSmoothGroup presentationTensorFormsGroup presentationTensorStableGroup
  presentationTensorSpaceGroup presentationTensorFiniteSpaceGroup padicCategoryLocalSpaceAddCommGroup

local instance (A : Subrepresentation T.realization.finiteRepresentation) :
    AddCommGroup A.toSubmodule := Submodule.addCommGroup _

/-- The remaining finite tensor factors and the infinite multiplicity of the actual cuspidal block. -/
abbrev localMultiplicityTail (v : FinitePlace F) :=
  LocalTensorTail (K := ℂ) F P.tensorExceptional v P.reference ⊗[ℂ]
    T.finiteInfiniteDecomposition.InfiniteSpace

set_option maxHeartbeats 650000 in
/-- The actual cuspidal block restricted to one place has its actual local component
on the first tensor factor and a trivial action on the complementary tensor. -/
def localMultiplicityEquiv
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (v : FinitePlace F) :
    Representation.Equiv
      (T.realization.finiteRepresentation.comp (localInclusion F (r + 1) v).toMonoidHom)
      ((P.localComponent v).representation.tprod
        (Representation.trivial ℂ (FiniteLocalGL F (r + 1) v) (P.localMultiplicityTail v))) := by
  classical
  let D := T.finiteInfiniteDecomposition
  let eFinite := P.finiteTensorEquiv hP
  let eLocal := localTensorSeparation F (r + 1) (fun w => (P.localFactor w).representation)
    P.tensorExceptional P.reference P.reference_fixed P.presentation.reference_nonzero v
  let eComponent := P.presentation.localComponentEquiv P.finiteSlice.nonzero v
  let W := (P.localComponent v).Space
  let X := P.localFactor v
  let Y := LocalTensorTail (K := ℂ) F P.tensorExceptional v P.reference
  let M := D.InfiniteSpace
  let e : W ⊗[ℂ] (Y ⊗[ℂ] M) ≃ₗ[ℂ] T.Space :=
    (TensorProduct.congr eComponent.symm.toLinearEquiv (LinearEquiv.refl ℂ (Y ⊗[ℂ] M))).trans
      ((TensorProduct.assoc ℂ X Y M).symm.trans
        ((TensorProduct.congr (eLocal.symm.toLinearEquiv.trans eFinite.toLinearEquiv)
          (LinearEquiv.refl ℂ M)).trans D.equiv))
  have he (x : W) (y : Y) (f : M) :
      e (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] f)) = f (eFinite (eLocal.symm (eComponent.symm x ⊗ₜ[ℂ] y))) := by
    rfl
  refine (Representation.Equiv.mk e (fun g => ?_)).symm
  apply TensorProduct.ext_threefold'
  intro x y f
  let d := localInclusion F (r + 1) v g
  change e (((P.localComponent v).representation g x) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] f)) =
    T.realization.finiteRepresentation d (e (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] f)))
  have hComponent : eComponent.symm ((P.localComponent v).representation g x) =
      (P.localFactor v).representation g (eComponent.symm x) :=
    IntertwiningMap.isIntertwining _ _ eComponent.symm.toIntertwiningMap g x
  let a := eLocal.symm (eComponent.symm x ⊗ₜ[ℂ] y)
  have hLocal : P.finiteTensorRepresentation d a =
      eLocal.symm ((P.localFactor v).representation g (eComponent.symm x) ⊗ₜ[ℂ] y) :=
    tensorLocalRepresentation_reassemble F (r + 1) (fun w => (P.localFactor w).representation)
      P.tensorExceptional P.reference P.reference_fixed P.presentation.reference_nonzero v g
      (eComponent.symm x) y
  calc
    _ = f (eFinite (eLocal.symm (eComponent.symm ((P.localComponent v).representation g x) ⊗ₜ[ℂ] y))) :=
      he _ y f
    _ = f (eFinite (eLocal.symm ((P.localFactor v).representation g (eComponent.symm x) ⊗ₜ[ℂ] y))) :=
      congrArg (fun w => f (eFinite (eLocal.symm (w ⊗ₜ[ℂ] y)))) hComponent
    _ = f (eFinite (P.finiteTensorRepresentation d a)) := congrArg (fun b => f (eFinite b)) hLocal.symm
    _ = f (D.finite.toRepresentation d (eFinite a)) :=
      congrArg f (IntertwiningMap.isIntertwining _ _ eFinite.toIntertwiningMap d a)
    _ = T.realization.finiteRepresentation d (f (eFinite a)) :=
      IntertwiningMap.isIntertwining _ _ f d (eFinite a)
    _ = _ := congrArg (T.realization.finiteRepresentation d) (he x y f).symm

end Automorphic.CuspidalSpectralPresentation

end Langlands
