import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChange

/-! # Naturality of the canonical comparison of dual abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The actual canonical dual base-change comparison commutes with the
contravariant dual of every actual abelian-scheme homomorphism. -/
def DualAbelianBaseChangeNaturalityStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (compatibility : DualAbelianBaseChangeStatement.{u})
    (S S' : Scheme.{u}) (b : S' ⟶ S) (A B : AbelianScheme S)
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (hA' : HasDualScheme ((baseChange b).obj A))
    (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
    (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))
    (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
      MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
        (dualScheme ((baseChange b).obj A) hA')))
    (hB' : HasDualScheme ((baseChange b).obj B))
    (geometryB' : DualSchemeGeometry ((baseChange b).obj B) hB')
    (MB' : LineBundle ((relativeSpace ((baseChange b).obj B).X.hom).obj
      (dualScheme ((baseChange b).obj B) hB')))
    (evaluationB' : tensorObj (poincareFamily ((baseChange b).obj B) hB').obj.carrier
      MB'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj B).X.hom).obj
        (dualScheme ((baseChange b).obj B) hB')))
    (f : A ⟶ B),
    (baseChange b).map
        (dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA
          stability composition unitCoherence associativity comparison symmetry
          hB geometryB MB evaluationB f) ≫
      (dualAbelianBaseChangeIso preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b A
        hA geometryA MA evaluationA hA' geometryA' MA' evaluationA').hom =
    (dualAbelianBaseChangeIso preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b B
        hB geometryB MB evaluationB hB' geometryB' MB' evaluationB').hom ≫
      dualAbelianSchemeMapFromEvaluation hA' geometryA' preservation MA' evaluationA'
        stability composition unitCoherence associativity comparison symmetry
        hB' geometryB' MB' evaluationB' ((baseChange b).map f)

end Langlands.AbelianScheme
