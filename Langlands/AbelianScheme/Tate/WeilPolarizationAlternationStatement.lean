import Langlands.AbelianScheme.Tate.WeilAlongHom
import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlternationStatement
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-! # Conditional alternation of the integral polarization Weil pairings -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

/-- Finite relative polarization alternation implies alternation of the actual
selected, away and prime-adic integral Weil pairings. -/
def IntegralPolarizationWeilAlternationStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (compatibility : RelativeFiniteWeilTransitionStatement.{u})
    (_alternation : RelativeFiniteWeilAlternationStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
      evaluationA stability composition unitCoherence associativity comparison symmetry),
      IsPolarization preservation square universality A hA geometryA MA evaluationA
        stability composition unitCoherence associativity comparison symmetry lam →
      ∀ (T : Over S),
        (∀ P : ℕ → Prop,
          (integralWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility T lam P).IsAlt) ∧
        (∀ m : ℕ,
          (awayWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility T lam m).IsAlt) ∧
        (∀ (p : ℕ) [Fact p.Prime],
          (primeWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility T p lam).IsAlt)

end Langlands.AbelianScheme
