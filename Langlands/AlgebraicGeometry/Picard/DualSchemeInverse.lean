import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroInverse
import Langlands.AlgebraicGeometry.Picard.DualSchemeMonoid

/-! # Inversion on a chosen dual from a supplied Poincare evaluation -/

universe u

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (M : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluation : tensorObj (poincareFamily A hA).obj.carrier M.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

/-- Classify the geometrically Picard-zero rigidification of a supplied
ordinary inverse of the Poincare bundle. -/
def dualInverseFromEvaluation : dualScheme A hA ⟶ dualScheme A hA :=
  dualClassify A hA (dualScheme A hA)
    (picardZeroInverseClass preservation A (poincareFamily A hA) M evaluation
      (poincareFamily_universal A hA).1)

variable (stability : PicardZeroPullbackStatement.{u})

lemma dualPointClass_inverseFromEvaluation :
    dualPointClass stability A hA (dualInverseFromEvaluation A hA preservation M evaluation) =
      picardZeroInverseClass preservation A (poincareFamily A hA) M evaluation
        (poincareFamily_universal A hA).1 :=
  dualPointClass_classify stability A hA _ _

/-- The identity point classifies the Poincare family itself. -/
lemma dualPointClass_id :
    dualPointClass stability A hA (𝟙 (dualScheme A hA)) =
      ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
        (poincareFamily A hA), (poincareFamily_universal A hA).1⟩ := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classifyingMap_id A.X.hom (unitSection A)
    (unitSection_comp A) Langlands.SchemeModule.RigidifiedModule.pullbackCoherence _

variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})

include composition unitCoherence in
/-- The classified inverse satisfies the inverse equation as a scheme morphism. -/
lemma dualTensor_right_inverseFromEvaluation :
    prod.lift (𝟙 (dualScheme A hA))
        (dualInverseFromEvaluation A hA preservation M evaluation) ≫
        dualTensor stability A hA preservation =
      (Over.homMk (dualScheme A hA).hom : dualScheme A hA ⟶ Over.mk (𝟙 S)) ≫
        dualOrigin A hA := by
  apply dualPointClass_injective stability A hA
  rw [dualTensor_points stability A hA preservation composition unitCoherence.1,
    dualPointClass_id, dualPointClass_inverseFromEvaluation, dualPointClass_origin]
  exact picardZeroClassesTensor_inverseClass preservation A _ M evaluation
    (poincareFamily_universal A hA).1

include composition unitCoherence in
/-- On every test scheme, postcomposition with the constructed inverse is
a right inverse for the actual dual multiplication. -/
lemma dualTensor_points_right_inverseFromEvaluation {T : Over S}
    (p : T ⟶ dualScheme A hA) :
    prod.lift p (p ≫ dualInverseFromEvaluation A hA preservation M evaluation) ≫
        dualTensor stability A hA preservation =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  calc
    _ = p ≫ (prod.lift (𝟙 (dualScheme A hA))
        (dualInverseFromEvaluation A hA preservation M evaluation) ≫
        dualTensor stability A hA preservation) := by
      simp only [← Category.assoc, prod.comp_lift, Category.comp_id]
    _ = p ≫ ((Over.homMk (dualScheme A hA).hom :
        dualScheme A hA ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :=
      congrArg (fun f ↦ p ≫ f)
        (dualTensor_right_inverseFromEvaluation A hA preservation M evaluation stability
          composition unitCoherence)
    _ = _ := by
      rw [← Category.assoc]
      congr 1
      apply Over.OverMorphism.ext
      exact p.w

variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

/-- The actual point monoid becomes a commutative group, with inverse given
by postcomposition with the classified inverse of the Poincare bundle. -/
@[instance_reducible]
def dualPointCommGroupFromEvaluation (T : Over S) : CommGroup (T ⟶ dualScheme A hA) where
  __ := dualPointCommMonoid stability A hA preservation composition unitCoherence
    associativity comparison symmetry T
  inv p := p ≫ dualInverseFromEvaluation A hA preservation M evaluation
  inv_mul_cancel p := by
    change prod.lift (p ≫ dualInverseFromEvaluation A hA preservation M evaluation) p ≫
      dualTensor stability A hA preservation =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA
    rw [dualTensor_points_comm stability A hA preservation composition unitCoherence.1 symmetry]
    exact dualTensor_points_right_inverseFromEvaluation A hA preservation M evaluation stability
      composition unitCoherence p

end Langlands.AbelianScheme
