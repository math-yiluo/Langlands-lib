import Langlands.AlgebraicGeometry.Picard.PicardZeroMonoid
import Langlands.AlgebraicGeometry.Picard.DualSchemeAssociativity

/-! # Commutative monoids of dual-scheme points -/

universe u

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (stability : PicardZeroPullbackStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

/-- The constructed multiplication and origin equip all dual-valued points with
their proved commutative-monoid structure. -/
@[instance_reducible]
def dualPointCommMonoid (T : Over S) : CommMonoid (T ⟶ dualScheme A hA) where
  mul f g := prod.lift f g ≫ dualTensor stability A hA preservation
  one := (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA
  mul_assoc := dualTensor_points_assoc stability A hA preservation composition unitCoherence.1
    associativity comparison
  one_mul f := by
    change prod.lift ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) f ≫
      dualTensor stability A hA preservation = f
    apply dualPointClass_injective stability A hA T
    rw [dualTensor_points stability A hA preservation composition unitCoherence.1,
      dualPointClass_origin, picardZeroClassesTensor_left_unit preservation A unitCoherence]
  mul_one f := by
    change prod.lift f ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) ≫
      dualTensor stability A hA preservation = f
    apply dualPointClass_injective stability A hA T
    rw [dualTensor_points stability A hA preservation composition unitCoherence.1,
      dualPointClass_origin, picardZeroClassesTensor_right_unit preservation A unitCoherence]
  mul_comm := dualTensor_points_comm stability A hA preservation composition unitCoherence.1
    symmetry

/-- Poincare-family classification is a multiplicative equivalence for the actual
point multiplication and geometric Picard-zero tensor. -/
def dualPointMulEquiv (T : Over S) :
    letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
      associativity comparison symmetry T
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    (T ⟶ dualScheme A hA) ≃* PicardZeroClasses A T := by
  letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
    associativity comparison symmetry T
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  exact
    { toFun := dualPointClass stability A hA
      invFun := dualClassify A hA T
      left_inv := dualClassify_pointClass stability A hA
      right_inv := dualPointClass_classify stability A hA T
      map_mul' := dualTensor_points stability A hA preservation composition unitCoherence.1 }

/-- Parameter precomposition preserves the actual dual-point multiplication and origin. -/
def dualPointPullbackMonoidHom {T U : Over S} (h : T ⟶ U) :
    letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
      associativity comparison symmetry U
    letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
      associativity comparison symmetry T
    (U ⟶ dualScheme A hA) →* (T ⟶ dualScheme A hA) := by
  letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
    associativity comparison symmetry U
  letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
    associativity comparison symmetry T
  exact
    { toFun := fun p ↦ h ≫ p
      map_one' := by
        change h ≫ ((Over.homMk U.hom : U ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) =
          (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA
        rw [← Category.assoc]
        congr 1
        apply Over.OverMorphism.ext
        exact h.w
      map_mul' := by
        intro p q
        change h ≫ (prod.lift p q ≫ dualTensor stability A hA preservation) =
          prod.lift (h ≫ p) (h ≫ q) ≫ dualTensor stability A hA preservation
        rw [← Category.assoc, prod.comp_lift] }

/-- The multiplicative classification equivalence commutes with parameter pullback. -/
lemma dualPointMulEquiv_naturality {T U : Over S} (h : T ⟶ U)
    (p : U ⟶ dualScheme A hA) :
    dualPointMulEquiv stability A hA preservation composition unitCoherence associativity
        comparison symmetry T
        (dualPointPullbackMonoidHom stability A hA preservation composition unitCoherence
          associativity comparison symmetry h p) =
      picardZeroClassesPullbackMonoidHom preservation unitCoherence associativity comparison
        symmetry A composition stability h
        (dualPointMulEquiv stability A hA preservation composition unitCoherence associativity
          comparison symmetry U p) :=
  dualPointClass_comp stability A hA h p

end Langlands.AbelianScheme
