import Langlands.AlgebraicGeometry.Picard.FieldDualAbelianScheme
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeMapAdditivityStatement

/-! # Conditional additive dualization over a field -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (additivity : FieldDualSchemeMapAdditivityStatement.{u})
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable {k : Type u} [Field k]
variable {A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
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

include additivity in
/-- Additivity of the actual dual group homomorphisms from the explicit scheme-map theorem. -/
lemma fieldDualGroupSchemeMap_add (f g : A ⟶ B) :
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
  rw [additivity preservation stability k A B hA hB f g]
  simp only [← Category.assoc, prod.comp_lift, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd]

/-- The actual dual group maps, bundled additively in the input homomorphism. -/
def fieldDualGroupSchemeMapAddHom : (A ⟶ B) →+ (GB ⟶ GA) :=
  AddMonoidHom.mk'
    (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB)
    (fieldDualGroupSchemeMap_add additivity preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB)

@[simp] lemma fieldDualGroupSchemeMapAddHom_apply (f : A ⟶ B) :
    fieldDualGroupSchemeMapAddHom additivity preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f =
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f := rfl

variable (geometry : FieldDualSchemeGeometryStatement.{u})

local notation "FA" => fieldDualAbelianSchemeFromEvaluation geometry A hA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "FB" => fieldDualAbelianSchemeFromEvaluation geometry B hB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry

/-- Additive dualization between the constructed dual abelian schemes. -/
def fieldDualAbelianSchemeMapAddHom : (A ⟶ B) →+ (FB ⟶ FA) :=
  fieldDualGroupSchemeMapAddHom additivity preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB

@[simp] lemma fieldDualAbelianSchemeMapAddHom_apply (f : A ⟶ B) :
    fieldDualAbelianSchemeMapAddHom additivity preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB geometry f =
    fieldDualAbelianSchemeMapFromEvaluation geometry hA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hB MB evaluationB f := rfl

end Langlands.AbelianScheme
