import Langlands.AbelianScheme.Tate.WeilIntegral
import Langlands.AlgebraicGeometry.Picard.RelativePolarization

/-! # Geometric-point nondegeneracy of the actual finite Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

/-- At a geometric point whose field has characteristic prime to `n`, the existing actual
finite Weil pairing `A[n] × A^t[n] → μ_n` on points has trivial left and right kernels. -/
def GeometricFiniteWeilNondegeneracyStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (_square : MumfordBundlePicardZeroStatement.{u})
    (_universality : PicardZeroUniversalBaseChangeStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (_compatibility : RelativeFiniteWeilTransitionStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A) (_geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), (n : K) ≠ 0 →
      (∀ x, (∀ y, finiteWeilLevelBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA MA evaluationA n (Over.mk s) x y = 0) →
        x = 0) ∧
      (∀ y, (∀ x, finiteWeilLevelBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA MA evaluationA n (Over.mk s) x y = 0) →
        y = 0)

end Langlands.AbelianScheme
