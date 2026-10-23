import Langlands.AlgebraicGeometry.Picard.DualGroupSchemeMap
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.FieldDualAbelianScheme

/-! # Conditional dual abelian schemes over a base scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (hA : HasDualScheme A)
variable (geometryA : DualSchemeGeometry A hA)
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

/-- Equip the constructed dual group scheme with the explicit geometry
of its actual parameter scheme. -/
def dualAbelianSchemeFromEvaluation :
    AbelianScheme S where
  toCommGroupScheme := dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry
  smooth := geometryA.1
  proper := geometryA.2.1
  geometricallyConnected := geometryA.2.2

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The actual universal parameter scheme is unchanged. -/
@[simp] lemma dualAbelianSchemeFromEvaluation_X :
    (DA).X = dualScheme A hA := rfl

/-- All group operations are those already constructed from Poincare classification. -/
@[simp] lemma dualAbelianSchemeFromEvaluation_toCommGroupScheme :
    (DA).toCommGroupScheme =
      dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA stability composition
        unitCoherence associativity comparison symmetry := rfl

/-- Poincare pullback gives the actual multiplicative classification on every test scheme. -/
def dualAbelianSchemePointMulEquiv
    (T : Over S) :
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    (T ⟶ (DA).X) ≃* PicardZeroClasses A T :=
  dualCommGroupSchemePointMulEquiv A hA preservation MA evaluationA stability composition
    unitCoherence associativity comparison symmetry T

@[simp] lemma dualAbelianSchemePointMulEquiv_apply
    (T : Over S) (p : T ⟶ (DA).X) :
    dualAbelianSchemePointMulEquiv A hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry T p =
        dualPointClass stability A hA p := rfl

variable {A}
variable {B : AbelianScheme S}
variable (hB : HasDualScheme B)
variable (geometryB : DualSchemeGeometry B hB)
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry

/-- The actual dual pullback map, now a homomorphism of the conditional abelian schemes. -/
def dualAbelianSchemeMapFromEvaluation (f : A ⟶ B) : DB ⟶ DA :=
  dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f

/-- Forgetting the abelian-scheme structure recovers the original dual scheme morphism. -/
lemma dualAbelianSchemeMapFromEvaluation_hom (f : A ⟶ B) :
    hom (dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hB geometryB MB evaluationB f) =
        (dualSchemeMap homPicardZeroPullback f hA hB).left := rfl

/-- The dual abelian-scheme map of the identity is the identity. -/
lemma dualAbelianSchemeMapFromEvaluation_id :
    dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hA geometryA MA evaluationA (𝟙 A) =
        𝟙 DA :=
  dualCommGroupSchemeMapFromEvaluation_id preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA

variable {C : AbelianScheme S}
variable (hC : HasDualScheme C)
variable (geometryC : DualSchemeGeometry C hC)
variable (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
variable (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
  structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))

/-- Dual abelian-scheme maps reverse composition. -/
lemma dualAbelianSchemeMapFromEvaluation_comp (f : A ⟶ B) (g : B ⟶ C) :
    dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hC geometryC MC evaluationC (f ≫ g) =
    dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB evaluationB stability
      composition unitCoherence associativity comparison symmetry hC geometryC MC evaluationC g ≫
    dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hB geometryB MB evaluationB f :=
  dualCommGroupSchemeMapFromEvaluation_comp preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB hC MC evaluationC f g

/-- On a field base, the general construction agrees with the published field construction. -/
lemma dualAbelianSchemeFromEvaluation_field (k : Type u) [Field k]
    (F : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hF : HasDualScheme F) (geometry : FieldDualSchemeGeometryStatement.{u})
    (MF : LineBundle ((relativeSpace F.X.hom).obj (dualScheme F hF)))
    (evaluationF : tensorObj (poincareFamily F hF).obj.carrier MF.obj ≅
      structureSheaf ((relativeSpace F.X.hom).obj (dualScheme F hF))) :
    dualAbelianSchemeFromEvaluation F hF (geometry k F hF) preservation MF evaluationF
      stability composition unitCoherence associativity comparison symmetry =
    fieldDualAbelianSchemeFromEvaluation geometry F hF preservation MF evaluationF
      stability composition unitCoherence associativity comparison symmetry := rfl

end Langlands.AbelianScheme
