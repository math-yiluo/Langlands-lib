import Langlands.AlgebraicGeometry.Modules.RigidificationTensor
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle

/-! # Tensor products of rigidified line bundles -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

variable (preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

/-- Tensor the rigidifications and retain the proved local rank-one property. -/
def tensor (L M : RigidifiedLineBundle ε) : RigidifiedLineBundle ε :=
  ⟨RigidifiedModule.tensorObj preservation L.obj M.obj,
    L.property.tensor preservation M.property⟩

/-- The tensor bifunctor on actual rigidified line bundles. -/
def tensorFunctor (ε : S ⟶ X) :
    RigidifiedLineBundle ε × RigidifiedLineBundle ε ⥤ RigidifiedLineBundle ε :=
  ObjectProperty.lift (fun M : RigidifiedModule ε ↦ IsLocallyFreeRankOne M.carrier)
    ((forgetToRigidified ε).prod (forgetToRigidified ε) ⋙
      RigidifiedModule.tensorFunctor preservation ε)
    (fun LM ↦ LM.1.property.tensor preservation LM.2.property)

lemma tensorFunctor_obj (L M : RigidifiedLineBundle ε) :
    (tensorFunctor preservation ε).obj (L, M) = tensor preservation L M := rfl

/-- Forgetting rank one recovers the rigidified-module tensor. -/
def tensorForgetToRigidifiedIso (ε : S ⟶ X) :
    tensorFunctor preservation ε ⋙ forgetToRigidified ε ≅
      (forgetToRigidified ε).prod (forgetToRigidified ε) ⋙
        RigidifiedModule.tensorFunctor preservation ε :=
  Iso.refl _

/-- Forgetting rigidification recovers the line-bundle tensor. -/
def tensorForgetIso (ε : S ⟶ X) :
    tensorFunctor preservation ε ⋙ forget ε ≅
      (forget ε).prod (forget ε) ⋙ LineBundle.tensorFunctor preservation X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; simp; rfl)

/-- Compatible isomorphisms induce an isomorphism of the tensor bundles. -/
def tensorIso {L L' M M' : RigidifiedLineBundle ε} (e : L ≅ L') (d : M ≅ M') :
    tensor preservation L M ≅ tensor preservation L' M' := by
  rw [← tensorFunctor_obj preservation L M, ← tensorFunctor_obj preservation L' M']
  exact (tensorFunctor preservation ε).mapIso (e.prod d)

variable (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

/-- Tensor induces a well-defined binary operation on relative rigidified classes. -/
def classesTensor (T : Over S) :
    Classes f ε section_eq T → Classes f ε section_eq T → Classes f ε section_eq T :=
  Quotient.map₂ (tensor preservation)
    (fun _ _ ⟨e⟩ _ _ ⟨d⟩ ↦ ⟨tensorIso preservation e d⟩)

/-- On representatives, the quotient operation is the actual rigidified tensor. -/
lemma classesTensor_classOf {T : Over S} (L M : relative f ε section_eq T) :
    classesTensor preservation f ε section_eq T
        (classOf f ε section_eq L) (classOf f ε section_eq M) =
      classOf f ε section_eq (tensor preservation L M) := rfl

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
