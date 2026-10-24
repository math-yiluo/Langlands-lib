import Langlands.AlgebraicGeometry.Picard.DualSchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.DualAbelianScheme

/-! # Group compatibility of the canonical dual base-change comparison -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The Poincare-compatible scheme comparison lifts to an isomorphism of the
constructed dual abelian schemes. Its underlying map is prescribed exactly. -/
def DualAbelianBaseChangeStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (S S' : Scheme.{u}) (b : S' ⟶ S) (A : AbelianScheme S)
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (hA' : HasDualScheme ((baseChange b).obj A))
    (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
    (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))
    (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
      MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
        (dualScheme ((baseChange b).obj A) hA'))),
    ∃ e : (baseChange b).obj
        (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
          stability composition unitCoherence associativity comparison symmetry) ≅
      dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA' geometryA' preservation
        MA' evaluationA' stability composition unitCoherence associativity comparison symmetry,
      (groupHom e.hom).hom.hom = (dualSchemeBaseChangeIso universality b A hA hA').hom

end Langlands.AbelianScheme
