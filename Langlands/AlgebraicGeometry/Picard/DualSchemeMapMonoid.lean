import Langlands.AlgebraicGeometry.Picard.DualSchemeMonoid
import Langlands.AlgebraicGeometry.Picard.DualSchemeMapTensor
import Langlands.AlgebraicGeometry.Picard.HomPicardZeroPullbackProof

/-! # Monoid homomorphisms induced by dual maps -/

universe u

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Actual homomorphism pullback is a monoid homomorphism on geometric Picard-zero classes. -/
def homPicardZeroPullbackMonoidHom (f : A ⟶ B) (T : Over S) :
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry B T
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    PicardZeroClasses B T →* PicardZeroClasses A T := by
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry B T
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  exact
    { toFun := homPicardZeroClassesPullback homPicardZeroPullback f T
      map_one' := homPicardZeroClassesPullback_trivial homPicardZeroPullback f T
      map_mul' := homPicardZeroClassesPullback_tensor preservation composition unitCoherence.1
        homPicardZeroPullback f T }

variable (stability : PicardZeroPullbackStatement.{u})

/-- Postcomposition by the constructed dual map preserves the actual point monoids. -/
def dualSchemeMapMonoidHom (f : A ⟶ B) (hA : HasDualScheme A) (hB : HasDualScheme B)
    (T : Over S) :
    letI := dualPointCommMonoid stability B hB preservation composition unitCoherence
      associativity comparison symmetry T
    letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
      associativity comparison symmetry T
    (T ⟶ dualScheme B hB) →* (T ⟶ dualScheme A hA) := by
  letI := dualPointCommMonoid stability B hB preservation composition unitCoherence
    associativity comparison symmetry T
  letI := dualPointCommMonoid stability A hA preservation composition unitCoherence
    associativity comparison symmetry T
  exact
    { toFun := fun p ↦ p ≫ dualSchemeMap homPicardZeroPullback f hA hB
      map_one' := by
        change ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin B hB) ≫
          dualSchemeMap homPicardZeroPullback f hA hB =
            (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA
        rw [Category.assoc, dualSchemeMap_origin]
      map_mul' := by
        intro p q
        change (prod.lift p q ≫ dualTensor stability B hB preservation) ≫
          dualSchemeMap homPicardZeroPullback f hA hB =
            prod.lift (p ≫ dualSchemeMap homPicardZeroPullback f hA hB)
              (q ≫ dualSchemeMap homPicardZeroPullback f hA hB) ≫
                dualTensor stability A hA preservation
        apply dualPointClass_injective stability A hA T
        rw [dualPointClass_dualSchemeMap,
          dualTensor_points stability B hB preservation composition unitCoherence.1,
          homPicardZeroClassesPullback_tensor preservation composition unitCoherence.1,
          dualTensor_points stability A hA preservation composition unitCoherence.1,
          dualPointClass_dualSchemeMap, dualPointClass_dualSchemeMap] }

/-- Under multiplicative Poincare classification, the dual-map homomorphism is
exactly the actual homomorphism pullback on Picard-zero classes. -/
lemma dualSchemeMapMonoidHom_classification (f : A ⟶ B) (hA : HasDualScheme A)
    (hB : HasDualScheme B) (T : Over S) (p : T ⟶ dualScheme B hB) :
    dualPointMulEquiv stability A hA preservation composition unitCoherence associativity
        comparison symmetry T
        (dualSchemeMapMonoidHom preservation composition unitCoherence associativity
          comparison symmetry stability f hA hB T p) =
      homPicardZeroPullbackMonoidHom preservation composition unitCoherence associativity
        comparison symmetry f T
        (dualPointMulEquiv stability B hB preservation composition unitCoherence associativity
          comparison symmetry T p) :=
  dualPointClass_dualSchemeMap homPicardZeroPullback stability f hA hB p

end Langlands.AbelianScheme
