import Langlands.AbelianScheme.Tate.WeilRationalPrimeAlongHom
import Langlands.AbelianScheme.Tate.WeilPolarizationAlternationStatement

/-! # Conditional alternation of rational and adelic polarization Weil pairings -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

/-- Relative finite polarization alternation implies alternation of the actual
rational selected, prime-adic, adelic and away adelic pullback pairings. -/
def RationalPolarizationWeilAlternationStatement : Prop :=
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
          (rationalWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility T lam P).IsAlt) ∧
        (∀ (p : ℕ) [Fact p.Prime],
          (primeRationalWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility T p lam).IsAlt) ∧
        (∀ (P : ℕ → Prop) (h : Global.RationalProfiniteIntegerAdeleComparison),
          let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
          let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
          (adelicWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility T lam P h).IsAlt) ∧
        (∀ (h : Global.RationalProfiniteIntegerAdeleComparison) (m : ℕ)
          (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m),
          let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
          let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
          (awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility T lam hAway).IsAlt)

end Langlands.AbelianScheme
