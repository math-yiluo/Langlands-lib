import Langlands.AlgebraicGeometry.Picard.DualAbelianScheme
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityStatement

/-! # Conditional additive dualization over a base scheme -/

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
variable (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "DA" => dualScheme A hA
local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GB" => dualCommGroupSchemeFromEvaluation B hB preservation MB evaluationB
  stability composition unitCoherence associativity comparison symmetry

include additivity in
/-- The endpoint-specific scheme-map equation gives addition of the actual group maps. -/
lemma dualGroupSchemeMap_add (f g : A ⟶ B) :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB (f + g) =
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f +
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB g := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  change dualSchemeMap homPicardZeroPullback (f + g) hA hB =
    CartesianMonoidalCategory.lift (dualSchemeMap homPicardZeroPullback f hA hB)
      (dualSchemeMap homPicardZeroPullback g hA hB) ≫
        (prod.lift (CartesianMonoidalCategory.fst DA DA) (CartesianMonoidalCategory.snd DA DA) ≫
          dualTensor stability A hA preservation)
  rw [additivity f g]
  simp only [← Category.assoc, prod.comp_lift, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd]

/-- Actual dualization bundled as an additive map between integral Hom groups. -/
def dualGroupSchemeMapAddHom : (A ⟶ B) →+ (GB ⟶ GA) :=
  AddMonoidHom.mk'
    (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB)
    (dualGroupSchemeMap_add preservation composition unitCoherence associativity comparison
      symmetry stability hA hB additivity MA evaluationA MB evaluationB)

@[simp] lemma dualGroupSchemeMapAddHom_apply (f : A ⟶ B) :
    dualGroupSchemeMapAddHom preservation composition unitCoherence associativity comparison
      symmetry stability hA hB additivity MA evaluationA MB evaluationB f =
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f := rfl

variable (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)

local notation "FA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "FB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry

/-- The same additive dualization between the constructed dual abelian schemes. -/
def dualAbelianSchemeMapAddHom : (A ⟶ B) →+ (FB ⟶ FA) :=
  dualGroupSchemeMapAddHom preservation composition unitCoherence associativity comparison
    symmetry stability hA hB additivity MA evaluationA MB evaluationB

@[simp] lemma dualAbelianSchemeMapAddHom_apply (f : A ⟶ B) :
    dualAbelianSchemeMapAddHom preservation composition unitCoherence associativity comparison
      symmetry stability hA hB additivity MA evaluationA MB evaluationB geometryA geometryB f =
    dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hB geometryB MB evaluationB f :=
  rfl

end Langlands.AbelianScheme
