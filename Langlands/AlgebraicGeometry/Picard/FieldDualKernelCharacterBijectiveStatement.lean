import Langlands.AlgebraicGeometry.Picard.DualKernelCharacter
import Langlands.AbelianScheme.IsogenySpecialization

/-! # All-test-scheme bijectivity of actual kernel characters over a field -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

/-- The actual intrinsic beta of a field isogeny is bijective on every test scheme.
No arbitrary character map or duality isomorphism is supplied as an input. -/
def FieldDualKernelCharacterBijectiveStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (k : Type u) [Field k]
    (A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A) (hB : HasDualScheme B)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (f : A ⟶ B), IsIsogeny f →
    ∀ (T : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))),
      Function.Bijective
        (dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
          associativity comparison symmetry MA evaluationA MB evaluationB T)

end Langlands.AbelianScheme
