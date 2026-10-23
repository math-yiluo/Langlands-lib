import Langlands.AlgebraicGeometry.Picard.DualGroupScheme
import Langlands.AlgebraicGeometry.Picard.DualSchemeMapMonoid

/-! # Actual dual maps as commutative-group-scheme homomorphisms -/

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
variable {S : Scheme.{u}} {A B : AbelianScheme S}
variable (hA : HasDualScheme A) (hB : HasDualScheme B)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "DA" => dualScheme A hA
local notation "DB" => dualScheme B hB
local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GB" => dualCommGroupSchemeFromEvaluation B hB preservation MB evaluationB
  stability composition unitCoherence associativity comparison symmetry

/-- Pullback of rigidified classes induces an actual homomorphism of the dual group schemes. -/
def dualCommGroupSchemeMapFromEvaluation (f : A ⟶ B) : GB ⟶ GA := by
  refine Additive.ofMul ?_
  refine Grp.homMk'' (dualSchemeMap homPicardZeroPullback f hA hB) ?_ ?_
  · change ((Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
        MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) ≫ dualOrigin B hB) ≫
      dualSchemeMap homPicardZeroPullback f hA hB =
        (Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
          MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA
    rw [Category.assoc, dualSchemeMap_origin]
  · change
      (prod.lift (CartesianMonoidalCategory.fst DB DB) (CartesianMonoidalCategory.snd DB DB) ≫
          dualTensor stability B hB preservation) ≫
        dualSchemeMap homPicardZeroPullback f hA hB =
      MonoidalCategory.tensorHom (dualSchemeMap homPicardZeroPullback f hA hB)
          (dualSchemeMap homPicardZeroPullback f hA hB) ≫
        (prod.lift (CartesianMonoidalCategory.fst DA DA) (CartesianMonoidalCategory.snd DA DA) ≫
          dualTensor stability A hA preservation)
    rw [Category.assoc, dualSchemeMap_tensor preservation composition unitCoherence.1]
    simp only [← Category.assoc, prod.comp_lift, prod.lift_fst, prod.lift_snd,
      CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.tensorHom_snd]

/-- The bundled homomorphism retains the previously constructed underlying dual map. -/
lemma dualCommGroupSchemeMapFromEvaluation_hom (f : A ⟶ B) :
    (Langlands.CommGroupScheme.groupHom
      (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
        comparison symmetry stability hA hB MA evaluationA MB evaluationB f)).hom.hom =
      dualSchemeMap homPicardZeroPullback f hA hB := rfl

/-- The dual group-scheme map of the identity is the identity. -/
lemma dualCommGroupSchemeMapFromEvaluation_id :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hA MA evaluationA MA evaluationA (𝟙 A) = 𝟙 GA := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact dualSchemeMap_id homPicardZeroPullback
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence A hA

variable {C : AbelianScheme S} (hC : HasDualScheme C)
variable (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
variable (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
  structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))

/-- Dual group-scheme maps reverse composition. -/
lemma dualCommGroupSchemeMapFromEvaluation_comp (f : A ⟶ B) (g : B ⟶ C) :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hC MA evaluationA MC evaluationC (f ≫ g) =
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hB hC MB evaluationB MC evaluationC g ≫
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact dualSchemeMap_comp homPicardZeroPullback
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f g hA hB hC

/-- On all test schemes, the group-scheme map classifies the actual pullback of classes. -/
lemma dualCommGroupSchemeMapFromEvaluation_classification (f : A ⟶ B) (T : Over S)
    (p : T ⟶ (GB).X) :
    dualCommGroupSchemePointMulEquiv A hA preservation MA evaluationA stability composition
        unitCoherence associativity comparison symmetry T
        ((Langlands.GroupScheme.pointsMap (Langlands.CommGroupScheme.groupHom
          (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
            comparison symmetry stability hA hB MA evaluationA MB evaluationB f))).app
              (Opposite.op T) p) =
      homPicardZeroPullbackMonoidHom preservation composition unitCoherence associativity
        comparison symmetry f T
        (dualCommGroupSchemePointMulEquiv B hB preservation MB evaluationB stability composition
          unitCoherence associativity comparison symmetry T p) :=
  dualPointClass_dualSchemeMap homPicardZeroPullback stability f hA hB p

end Langlands.AbelianScheme
