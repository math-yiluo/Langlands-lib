import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroStatement
import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # The scheme morphism classifying the Mumford family -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
variable (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)

/-- The actual Mumford class, equipped with the explicit theorem-of-the-square consequence. -/
def mumfordPicardZeroClass : PicardZeroClasses A A.X :=
  ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
    (mumfordBundle A preservation L M evaluation),
    square preservation S A L M evaluation⟩

variable (hA : HasDualScheme A)

/-- The morphism to the actual universal parameter scheme classifying the Mumford family. -/
def mumfordSchemeMap : A.X ⟶ dualScheme A hA :=
  dualClassify A hA A.X (mumfordPicardZeroClass preservation square A L M evaluation)

/-- Poincare pullback along the constructed morphism has precisely the Mumford class. -/
lemma mumfordSchemeMap_spec :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) A.X
      (mumfordSchemeMap preservation square A L M evaluation hA) =
        RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
          (mumfordBundle A preservation L M evaluation) :=
  dualClassify_spec A hA A.X _

/-- The classifying equation is witnessed by an actual rigidified line-bundle isomorphism. -/
def mumfordSchemeMapPullbackIso :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (mumfordSchemeMap preservation square A L M evaluation hA)).obj
        (poincareFamily A hA) ≅ mumfordBundle A preservation L M evaluation :=
  dualClassifyPullbackIso A hA (mumfordBundle A preservation L M evaluation)
    (square preservation S A L M evaluation)

/-- A map with the same actual rigidified pullback equals the constructed map. -/
lemma mumfordSchemeMap_unique (f : A.X ⟶ dualScheme A hA)
    (e : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      f).obj (poincareFamily A hA) ≅ mumfordBundle A preservation L M evaluation) :
    f = mumfordSchemeMap preservation square A L M evaluation hA :=
  dualClassify_unique A hA A.X _ f (Quotient.sound ⟨e⟩)

/-- On every test scheme, the map classifies the parameter pullback of the Mumford family. -/
lemma mumfordSchemeMap_points (T : Over S) (a : T ⟶ A.X) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) T
      (a ≫ mumfordSchemeMap preservation square A L M evaluation hA) =
        RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A) a).obj (mumfordBundle A preservation L M evaluation)) := by
  rw [RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence, mumfordSchemeMap_spec]
  rfl

end Langlands.AbelianScheme
