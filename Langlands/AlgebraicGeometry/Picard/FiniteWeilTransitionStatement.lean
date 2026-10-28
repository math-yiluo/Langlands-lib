import Langlands.AlgebraicGeometry.Picard.FiniteWeilPairing
import Langlands.AbelianScheme.Tate.FiniteMonodromy

/-! # Divisibility compatibility of the actual finite Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

/-- The actual finite Weil pairings commute with the actual divisibility transitions.
This is a relative theorem target, not a proof of transition compatibility. -/
def RelativeFiniteWeilTransitionStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (n m : ℕ), 0 < n → 0 < m → ∀ (h : n ∣ m),
      let GA := dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
        stability composition unitCoherence associativity comparison symmetry
      prod.map (Langlands.GroupScheme.Tate.kernelTransition A.toGrp h)
          (Langlands.GroupScheme.Tate.kernelTransition (Langlands.CommGroupScheme.toGrp GA) h) ≫
        finiteWeilPairing preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n =
      finiteWeilPairing preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA m ≫
        (Langlands.CommGroupScheme.groupHom (mu.transition S h)).hom.hom

end Langlands.AbelianScheme
