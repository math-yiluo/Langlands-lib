import Langlands.AlgebraicGeometry.Picard.MumfordSchemeMapHomomorphismStatement
import Langlands.AlgebraicGeometry.Picard.DualAbelianScheme

/-! # The Mumford morphism as a homomorphism of abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
variable (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
variable (hA : HasDualScheme A)
variable (homomorphism :
  MumfordSchemeMapHomomorphism preservation stability square A L M evaluation hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "D" => dualScheme A hA
local notation "G" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "f" => mumfordSchemeMap preservation square A L M evaluation hA

/-- Bundle the actual Mumford map using its explicit unit and multiplication equations. -/
def mumfordCommGroupSchemeHom : A.toCommGroupScheme ⟶ G := by
  refine Additive.ofMul ?_
  refine Grp.homMk'' f ?_ ?_
  · exact homomorphism.1
  · change μ[A.X] ≫ f =
      MonoidalCategory.tensorHom f f ≫
        (prod.lift (CartesianMonoidalCategory.fst D D)
          (CartesianMonoidalCategory.snd D D) ≫ dualTensor stability A hA preservation)
    rw [homomorphism.2]
    simp only [← Category.assoc, prod.comp_lift,
      CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.tensorHom_snd]

/-- The bundled group-scheme morphism retains the actual classifying morphism. -/
lemma mumfordCommGroupSchemeHom_hom :
    (Langlands.CommGroupScheme.groupHom
      (mumfordCommGroupSchemeHom preservation composition unitCoherence associativity comparison
        symmetry stability square A L M evaluation hA homomorphism MA evaluationA)).hom.hom =
      f := rfl

variable (geometryA : DualSchemeGeometry A hA)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The homomorphism associated to the rigidified line bundle, with all geometric
and theorem inputs explicit. -/
def mumfordHom : A ⟶ DA :=
  mumfordCommGroupSchemeHom preservation composition unitCoherence associativity comparison
    symmetry stability square A L M evaluation hA homomorphism MA evaluationA

/-- Forgetting the bundled homomorphism recovers the original scheme morphism. -/
lemma mumfordHom_hom :
    hom (mumfordHom preservation composition unitCoherence associativity comparison symmetry
      stability square A L M evaluation hA homomorphism MA evaluationA geometryA) = (f).left := rfl

/-- The Poincare pullback of the bundled homomorphism is the actual Mumford family. -/
def mumfordHomPullbackIso :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (groupHom (mumfordHom preservation composition unitCoherence associativity comparison
        symmetry stability square A L M evaluation hA homomorphism MA evaluationA
          geometryA)).hom.hom).obj (poincareFamily A hA) ≅
      mumfordBundle A preservation L M evaluation :=
  mumfordSchemeMapPullbackIso preservation square A L M evaluation hA

/-- The actual Poincare pullback uniquely determines the bundled homomorphism. -/
lemma mumfordHom_unique (g : A ⟶ DA)
    (e : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (groupHom g).hom.hom).obj (poincareFamily A hA) ≅
        mumfordBundle A preservation L M evaluation) :
    g = mumfordHom preservation composition unitCoherence associativity comparison symmetry
      stability square A L M evaluation hA homomorphism MA evaluationA geometryA := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact mumfordSchemeMap_unique preservation square A L M evaluation hA _ e

/-- On every test scheme, the bundled homomorphism classifies parameter pullback
of the constructed Mumford family. -/
lemma mumfordHom_points (T : Over S) (a : T ⟶ A.X) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) T
      ((Langlands.GroupScheme.pointsMap
        (groupHom (mumfordHom preservation composition unitCoherence associativity comparison
          symmetry stability square A L M evaluation hA homomorphism MA evaluationA
            geometryA))).app (Opposite.op T) a) =
      RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) a).obj (mumfordBundle A preservation L M evaluation)) :=
  mumfordSchemeMap_points preservation square A L M evaluation hA T a

end Langlands.AbelianScheme
