import Langlands.AlgebraicGeometry.Picard.FiniteWeilPairing
import Langlands.AbelianScheme.Tate.FiniteMonodromy

/-! # Dual-homomorphism compatibility of the actual finite Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

/-- The actual finite Weil pairing is compatible with an actual homomorphism
and its constructed dual. This is a relative theorem target, not a proof. -/
def RelativeFiniteWeilFunctorialityStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A B : AbelianScheme S)
    (hA : HasDualScheme A) (hB : HasDualScheme B)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (f : A ⟶ B) (n : ℕ), 0 < n →
      let df := dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence
        associativity comparison symmetry stability hA hB MA evaluationA MB evaluationB f
      prod.map
          (Langlands.GroupScheme.Tate.kernelLevelMap (groupHom (A := A) (B := B) f) n)
          (𝟙 _) ≫
        finiteWeilPairing preservation composition unitCoherence associativity comparison
          symmetry stability hB MB evaluationB n =
      prod.map (𝟙 _)
          (Langlands.GroupScheme.Tate.kernelLevelMap
            (Langlands.CommGroupScheme.groupHom df) n) ≫
        finiteWeilPairing preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n

end Langlands.AbelianScheme
