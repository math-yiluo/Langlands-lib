import Langlands.AlgebraicGeometry.Picard.MumfordHomomorphism

/-! # The Mumford construction for an ordinary line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (L : LineBundle A.X.left) (B : LineBundle S)
variable (evaluationB :
  tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)

local notation "N" => LineBundle.normalize preservation A.X.hom (unitSection A)
  (unitSection_comp A) L B evaluationB

variable (M : LineBundle A.X.left)
variable (evaluation :
  tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)

/-- Normalize along the unit before forming the actual rigidified Mumford family. -/
def mumfordFamilyOfLineBundle : RigidifiedFamily A A.X :=
  mumfordBundle A preservation N M evaluation

/-- The ordinary bundle underlying this family includes normalization's base factor. -/
lemma mumfordFamilyOfLineBundle_forget :
    (RigidifiedLineBundle.forget (mumfordSection A)).obj
        (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation) =
      LineBundle.tensor preservation
        (LineBundle.tensor preservation
          ((LineBundle.pullback (mumfordAddition A)).obj
            (LineBundle.tensor preservation L ((LineBundle.pullback A.X.hom).obj B)))
          ((LineBundle.pullback (Limits.pullback.fst A.X.hom A.X.hom)).obj M))
        ((LineBundle.pullback (Limits.pullback.snd A.X.hom A.X.hom)).obj M) := rfl

variable (square : MumfordBundlePicardZeroStatement.{u}) (hA : HasDualScheme A)

/-- The scheme morphism classifying the normalized family's actual rigidified class. -/
def mumfordSchemeMapOfLineBundle : A.X ⟶ dualScheme A hA :=
  mumfordSchemeMap preservation square A N M evaluation hA

/-- Its Poincare pullback is isomorphic to the normalized family, including rigidification. -/
def mumfordSchemeMapOfLineBundlePullbackIso :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)).obj
        (poincareFamily A hA) ≅
      mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation :=
  mumfordSchemeMapPullbackIso preservation square A N M evaluation hA

/-- Uniqueness holds for maps with the same actual rigidified Poincare pullback. -/
lemma mumfordSchemeMapOfLineBundle_unique (g : A.X ⟶ dualScheme A hA)
    (e : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      g).obj (poincareFamily A hA) ≅
        mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation) :
    g = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA :=
  mumfordSchemeMap_unique preservation square A N M evaluation hA g e

/-- The normalized family is classified on every test scheme. -/
lemma mumfordSchemeMapOfLineBundle_points (T : Over S) (a : T ⟶ A.X) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) T
      (a ≫ mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA) =
        RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A) a).obj
              (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation)) :=
  mumfordSchemeMap_points preservation square A N M evaluation hA T a

variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable (homomorphism :
  MumfordSchemeMapHomomorphism preservation stability square A
    (LineBundle.normalize preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB) M evaluation hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (geometryA : DualSchemeGeometry A hA)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The homomorphism associated to an ordinary line bundle by unit-section normalization. -/
def mumfordHomOfLineBundle : A ⟶ DA :=
  mumfordHom preservation composition unitCoherence associativity comparison symmetry
    stability square A N M evaluation hA homomorphism MA evaluationA geometryA

/-- Its underlying scheme morphism is exactly the normalized-family classifier. -/
lemma mumfordHomOfLineBundle_hom :
    hom (mumfordHomOfLineBundle preservation A L B evaluationB M evaluation square hA
      composition unitCoherence associativity comparison symmetry stability
      homomorphism MA evaluationA geometryA) =
        (mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA).left :=
  rfl

/-- The bundled homomorphism retains the actual rigidified classification isomorphism. -/
def mumfordHomOfLineBundlePullbackIso :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (groupHom (mumfordHomOfLineBundle preservation A L B evaluationB M evaluation square hA
        composition unitCoherence associativity comparison symmetry stability
        homomorphism MA evaluationA geometryA)).hom.hom).obj (poincareFamily A hA) ≅
      mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation :=
  mumfordHomPullbackIso preservation composition unitCoherence associativity comparison symmetry
    stability square A N M evaluation hA homomorphism MA evaluationA geometryA

/-- The rigidified pullback property uniquely determines the bundled homomorphism. -/
lemma mumfordHomOfLineBundle_unique (g : A ⟶ DA)
    (e : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (groupHom g).hom.hom).obj (poincareFamily A hA) ≅
        mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation) :
    g = mumfordHomOfLineBundle preservation A L B evaluationB M evaluation square hA
      composition unitCoherence associativity comparison symmetry stability
      homomorphism MA evaluationA geometryA :=
  mumfordHom_unique preservation composition unitCoherence associativity comparison symmetry
    stability square A N M evaluation hA homomorphism MA evaluationA geometryA g e

end Langlands.AbelianScheme
