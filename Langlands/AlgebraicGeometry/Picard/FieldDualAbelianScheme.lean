import Langlands.AlgebraicGeometry.Picard.DualGroupSchemeMap
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryStatement

/-! # Conditional dual abelian schemes over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (geometry : FieldDualSchemeGeometryStatement.{u})
variable {k : Type u} [Field k]
variable (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
variable (hA : HasDualScheme A)
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

/-- Equip the constructed dual group scheme with the explicitly supplied field geometry. -/
def fieldDualAbelianSchemeFromEvaluation :
    AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) where
  toCommGroupScheme := dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry
  smooth := (geometry k A hA).1
  proper := (geometry k A hA).2.1
  geometricallyConnected := (geometry k A hA).2.2

local notation "DA" => fieldDualAbelianSchemeFromEvaluation geometry A hA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The actual universal parameter scheme is unchanged. -/
@[simp] lemma fieldDualAbelianSchemeFromEvaluation_X :
    (DA).X = dualScheme A hA := rfl

/-- All group operations are those already constructed from Poincare classification. -/
@[simp] lemma fieldDualAbelianSchemeFromEvaluation_toCommGroupScheme :
    (DA).toCommGroupScheme =
      dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA stability composition
        unitCoherence associativity comparison symmetry := rfl

/-- Poincare pullback gives the actual multiplicative classification on every test scheme. -/
def fieldDualAbelianSchemePointMulEquiv
    (T : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) :
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    (T ⟶ (DA).X) ≃* PicardZeroClasses A T :=
  dualCommGroupSchemePointMulEquiv A hA preservation MA evaluationA stability composition
    unitCoherence associativity comparison symmetry T

@[simp] lemma fieldDualAbelianSchemePointMulEquiv_apply
    (T : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) (p : T ⟶ (DA).X) :
    fieldDualAbelianSchemePointMulEquiv geometry A hA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry T p =
        dualPointClass stability A hA p := rfl

variable {A}
variable {B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
variable (hB : HasDualScheme B)
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "DB" => fieldDualAbelianSchemeFromEvaluation geometry B hB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry

/-- The actual dual pullback map, now a homomorphism of the conditional abelian schemes. -/
def fieldDualAbelianSchemeMapFromEvaluation (f : A ⟶ B) : DB ⟶ DA :=
  dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f

/-- Forgetting the abelian-scheme structure recovers the original dual scheme morphism. -/
lemma fieldDualAbelianSchemeMapFromEvaluation_hom (f : A ⟶ B) :
    hom (fieldDualAbelianSchemeMapFromEvaluation geometry hA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hB MB evaluationB f) =
        (dualSchemeMap homPicardZeroPullback f hA hB).left := rfl

/-- The dual abelian-scheme map of the identity is the identity. -/
lemma fieldDualAbelianSchemeMapFromEvaluation_id :
    fieldDualAbelianSchemeMapFromEvaluation geometry hA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hA MA evaluationA (𝟙 A) =
        𝟙 DA :=
  dualCommGroupSchemeMapFromEvaluation_id preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA

variable {C : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
variable (hC : HasDualScheme C)
variable (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
variable (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
  structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))

/-- Dual abelian-scheme maps reverse composition. -/
lemma fieldDualAbelianSchemeMapFromEvaluation_comp (f : A ⟶ B) (g : B ⟶ C) :
    fieldDualAbelianSchemeMapFromEvaluation geometry hA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hC MC evaluationC (f ≫ g) =
    fieldDualAbelianSchemeMapFromEvaluation geometry hB preservation MB evaluationB stability
      composition unitCoherence associativity comparison symmetry hC MC evaluationC g ≫
    fieldDualAbelianSchemeMapFromEvaluation geometry hA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hB MB evaluationB f :=
  dualCommGroupSchemeMapFromEvaluation_comp preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB hC MC evaluationC f g

end Langlands.AbelianScheme
