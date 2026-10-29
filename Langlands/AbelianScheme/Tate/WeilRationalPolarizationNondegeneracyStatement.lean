import Langlands.AbelianScheme.Tate.WeilRationalAlongHom
import Langlands.AlgebraicGeometry.Picard.RelativePolarization

/-! # Geometric-point nondegeneracy of full and away polarization Weil pairings -/

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

/-- At a characteristic-zero geometric point, an actual polarization gives
nondegenerate full and away rational and adelic Weil pairings. -/
def RationalPolarizationWeilNondegeneracyStatement : Prop :=
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
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
      evaluationA stability composition unitCoherence associativity comparison symmetry),
      IsPolarization preservation square universality A hA geometryA MA evaluationA
        stability composition unitCoherence associativity comparison symmetry lam →
      ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
        (s : Spec (CommRingCat.of K) ⟶ S),
        (rationalWeilAlongHomBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA geometryA MA evaluationA
          compatibility (Over.mk s) lam (fun _ => True)).Nondegenerate ∧
        (∀ m : ℕ,
          (rationalWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility (Over.mk s) lam (fun n => Nat.Coprime n m)).Nondegenerate) ∧
        (∀ h : Global.RationalProfiniteIntegerAdeleComparison,
          let := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
          let := TateTwist.Divisibility.finiteAdeleModule
            Γ((Over.mk s).left, ⊤) (fun _ => True) h
          (adelicWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility (Over.mk s) lam (fun _ => True) h).Nondegenerate) ∧
        (∀ (h : Global.RationalProfiniteIntegerAdeleComparison) (m : ℕ)
          (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m),
          let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
          let := TateTwist.Divisibility.primeToFiniteAdeleModule
            Γ((Over.mk s).left, ⊤) hAway
          (awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility (Over.mk s) lam hAway).Nondegenerate)

end Langlands.AbelianScheme
