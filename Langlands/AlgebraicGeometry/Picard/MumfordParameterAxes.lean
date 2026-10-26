import Langlands.AlgebraicGeometry.Picard.MumfordUnit
import Langlands.AlgebraicGeometry.Picard.MumfordBundleParameterAdditivityStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorPullback
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs

/-! # Unit-axis restrictions of the actual Mumford parameter-additivity equation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidalCategory

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The parameter axis `x ↦ (x,e)`. -/
def mumfordParameterFirstAxis : A.X ⟶ A.X ⊗ A.X :=
  CartesianMonoidalCategory.lift (𝟙 A.X) (1 : A.X ⟶ A.X)

/-- The parameter axis `y ↦ (e,y)`. -/
def mumfordParameterSecondAxis : A.X ⟶ A.X ⊗ A.X :=
  CartesianMonoidalCategory.lift (1 : A.X ⟶ A.X) (𝟙 A.X)

@[simp] lemma mumfordParameterFirstAxis_mul :
    mumfordParameterFirstAxis A ≫ μ[A.X] = 𝟙 A.X := by
  change (𝟙 A.X : A.X ⟶ A.X) * 1 = 𝟙 A.X
  exact mul_one _

@[simp] lemma mumfordParameterSecondAxis_mul :
    mumfordParameterSecondAxis A ≫ μ[A.X] = 𝟙 A.X := by
  change (1 : A.X ⟶ A.X) * 𝟙 A.X = 𝟙 A.X
  exact one_mul _

private lemma classesPullback_comp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V)
    (q : RigidifiedClasses A V) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) h
      (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) k q) =
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
      (h ≫ k) q := by
  refine Quotient.inductionOn q (fun F ↦ ?_)
  exact Quotient.sound ⟨(RigidifiedLineBundle.relativePullbackComp
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence A.X.hom (unitSection A)
      (unitSection_comp A) h k).app F⟩

private lemma classesPullback_id {T : Over S} (q : RigidifiedClasses A T) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
      (𝟙 T) q = q := by
  refine Quotient.inductionOn q (fun F ↦ ?_)
  exact Quotient.sound ⟨(RigidifiedLineBundle.relativePullbackId
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence A.X.hom (unitSection A)
      (unitSection_comp A) T).app F⟩

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
variable (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)

/-- The actual class of the parameter-first Mumford family. -/
abbrev mumfordBundleClass : RigidifiedClasses A A.X :=
  RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
    (mumfordBundle A preservation L M evaluation)

/-- Pullback of the actual Mumford class at the unit parameter is trivial. -/
lemma mumfordBundleClass_one (T : Over S) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
      (1 : T ⟶ A.X) (mumfordBundleClass A preservation L M evaluation) =
    RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)) :=
  Quotient.sound ⟨mumfordZeroParameterIso A preservation L M evaluation T⟩

/-- The two full families in the additivity equation agree on the first unit axis. -/
lemma mumfordBundleParameterAdditivity_firstAxis :
    let q := mumfordBundleClass A preservation L M evaluation
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (mumfordParameterFirstAxis A) (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) μ[A.X] q) =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (mumfordParameterFirstAxis A)
        (RigidifiedLineBundle.classesTensor preservation A.X.hom (unitSection A)
          (unitSection_comp A) (A.X ⊗ A.X)
          (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (CartesianMonoidalCategory.fst A.X A.X) q)
          (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (CartesianMonoidalCategory.snd A.X A.X) q)) := by
  dsimp only
  rw [classesPullback_comp A, mumfordParameterFirstAxis_mul, classesPullback_id A,
    RigidifiedLineBundle.classesPullback_tensor preservation pullbackTensorComposition
      pullbackTensorUnitCoherence.1,
    classesPullback_comp A, classesPullback_comp A]
  simp only [mumfordParameterFirstAxis, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd]
  rw [classesPullback_id A, mumfordBundleClass_one]
  exact (RigidifiedLineBundle.classesTensor_right_unit preservation pullbackTensorUnitCoherence
    A.X.hom (unitSection A) (unitSection_comp A) A.X _).symm

/-- The two full families in the additivity equation agree on the second unit axis. -/
lemma mumfordBundleParameterAdditivity_secondAxis :
    let q := mumfordBundleClass A preservation L M evaluation
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (mumfordParameterSecondAxis A) (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) μ[A.X] q) =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (mumfordParameterSecondAxis A)
        (RigidifiedLineBundle.classesTensor preservation A.X.hom (unitSection A)
          (unitSection_comp A) (A.X ⊗ A.X)
          (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (CartesianMonoidalCategory.fst A.X A.X) q)
          (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) (CartesianMonoidalCategory.snd A.X A.X) q)) := by
  dsimp only
  rw [classesPullback_comp A, mumfordParameterSecondAxis_mul, classesPullback_id A,
    RigidifiedLineBundle.classesPullback_tensor preservation pullbackTensorComposition
      pullbackTensorUnitCoherence.1,
    classesPullback_comp A, classesPullback_comp A]
  simp only [mumfordParameterSecondAxis, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd]
  rw [classesPullback_id A, mumfordBundleClass_one]
  exact (RigidifiedLineBundle.classesTensor_left_unit preservation pullbackTensorUnitCoherence
    A.X.hom (unitSection A) (unitSection_comp A) A.X _).symm

end Langlands.AbelianScheme
