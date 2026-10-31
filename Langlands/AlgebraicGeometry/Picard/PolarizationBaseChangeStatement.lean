import Langlands.AlgebraicGeometry.Picard.RelativePolarization

/-! # Stability of the full relative polarization predicate under canonical base change -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- A relative polarization remains a relative polarization after actual base
change and the canonical comparison with the dual of the changed abelian scheme. -/
def PolarizationBaseChangeStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (compatibility : DualAbelianBaseChangeStatement.{u})
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
        (dualScheme ((baseChange b).obj A) hA')))
    (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
      stability composition unitCoherence associativity comparison symmetry),
    IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam →
    IsPolarization preservation square universality ((baseChange b).obj A)
      hA' geometryA' MA' evaluationA' stability composition unitCoherence associativity
      comparison symmetry
      (dualAbelianBaseChangeMap preservation stability composition unitCoherence associativity
        comparison symmetry universality compatibility b A hA geometryA MA evaluationA
        hA' geometryA' MA' evaluationA' lam)

end Langlands.AbelianScheme
