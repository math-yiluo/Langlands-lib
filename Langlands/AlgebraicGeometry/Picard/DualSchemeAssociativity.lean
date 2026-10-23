import Langlands.AlgebraicGeometry.Picard.DualSchemeTensor
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorAssociativity

/-! # Associative tensor multiplication on a chosen dual scheme -/

universe u
open CategoryTheory AlgebraicGeometry Limits
noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (stability : PicardZeroPullbackStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorLeftUnitorStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})

include composition unitCoherence associativity comparison in
/-- The chosen dual multiplication is associative on every test scheme. -/
lemma dualTensor_points_assoc {T : Over S} (f g h : T ⟶ dualScheme A hA) :
    prod.lift (prod.lift f g ≫ dualTensor stability A hA preservation) h ≫
        dualTensor stability A hA preservation =
      prod.lift f (prod.lift g h ≫ dualTensor stability A hA preservation) ≫
        dualTensor stability A hA preservation := by
  apply dualPointClass_injective stability A hA T
  simp only [dualTensor_points stability A hA preservation composition unitCoherence]
  exact picardZeroClassesTensor_assoc preservation associativity comparison A T _ _ _

include composition unitCoherence associativity comparison in
/-- Associativity as an equality of morphisms from the left-associated triple product. -/
lemma dualTensor_assoc :
    prod.lift
        ((prod.fst : (dualScheme A hA ⨯ dualScheme A hA) ⨯ dualScheme A hA ⟶
          dualScheme A hA ⨯ dualScheme A hA) ≫ dualTensor stability A hA preservation)
        prod.snd ≫ dualTensor stability A hA preservation =
      prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫
          dualTensor stability A hA preservation) ≫ dualTensor stability A hA preservation := by
  have h := dualTensor_points_assoc stability A hA preservation composition unitCoherence
    associativity comparison
    ((prod.fst : (dualScheme A hA ⨯ dualScheme A hA) ⨯ dualScheme A hA ⟶
      dualScheme A hA ⨯ dualScheme A hA) ≫ prod.fst)
    (prod.fst ≫ prod.snd) prod.snd
  simpa only [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id] using h

/-- The actual multiplication on points, with its proved associative law. -/
@[instance_reducible]
def dualPointSemigroup (T : Over S) : Semigroup (T ⟶ dualScheme A hA) where
  mul f g := prod.lift f g ≫ dualTensor stability A hA preservation
  mul_assoc f g h := dualTensor_points_assoc stability A hA preservation composition
    unitCoherence associativity comparison f g h

end Langlands.AbelianScheme
