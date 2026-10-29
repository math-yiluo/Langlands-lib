import Langlands.AbelianScheme.Tate.WeilRationalPrimeAlongHom
import Langlands.AlgebraicGeometry.Picard.RelativePolarization

/-! # Geometric-point nondegeneracy of rational prime-adic polarization pairings -/

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

/-- An actual polarization gives a nondegenerate rational prime-adic Weil
pairing at a geometric point whose field has characteristic different from p. -/
def PrimeRationalPolarizationWeilNondegeneracyStatement : Prop :=
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
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S) (p : ℕ) [Fact p.Prime],
        (p : K) ≠ 0 →
        (primeRationalWeilAlongHomBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA geometryA MA evaluationA
          compatibility (Over.mk s) p lam).Nondegenerate

end Langlands.AbelianScheme
