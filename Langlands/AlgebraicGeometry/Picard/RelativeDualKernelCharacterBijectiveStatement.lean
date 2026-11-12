import Langlands.AlgebraicGeometry.Picard.DualKernelCharacter
import Langlands.AbelianScheme.IsogenySpecialization

/-! # All-test-scheme Cartier kernel duality over an arbitrary base -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

/-- The normalized Poincare character of an actual relative isogeny is bijective
on every test scheme. This is an explicit mathematical proof target. -/
def RelativeDualKernelCharacterBijectiveStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (S : Scheme.{u}) (A B : AbelianScheme S)
    (hA : HasDualScheme A) (hB : HasDualScheme B)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (f : A ⟶ B), IsIsogeny f →
    ∀ (T : Over S),
      Function.Bijective
        (dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
          associativity comparison symmetry MA evaluationA MB evaluationB T)

end Langlands.AbelianScheme
