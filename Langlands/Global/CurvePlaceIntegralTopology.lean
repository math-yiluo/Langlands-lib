import Langlands.Global.CurvePlaceIntegralTensor
import Langlands.Global.AdelicLocalFactorUnitsProof
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.Equiv

/-! # The actual finite-module topology on function-field completed integers -/

noncomputable section

universe u v

open scoped Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralTensor

namespace Langlands.Global

/-- A finite Hausdorff topological module over a compact topological ring
has its canonical finite-module topology. -/
theorem compactFiniteModuleIsModuleTopology
    (R : Type u) (M : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [TopologicalSpace M] [T2Space M] [IsTopologicalAddGroup M] [ContinuousSMul R M] :
    IsModuleTopology R M := by
  let : TopologicalSpace (ULift.{0} M) := moduleTopology R (ULift.{0} M)
  let : ContinuousAdd (ULift.{0} M) := ModuleTopology.continuousAdd R (ULift.{0} M)
  let : ContinuousSMul R (ULift.{0} M) := ModuleTopology.continuousSMul R (ULift.{0} M)
  let : CompactSpace (ULift.{0} M) := Module.Finite.compactSpace R (ULift.{0} M)
  let e : ULift.{0} M ≃ₗ[R] M := ULift.moduleEquiv
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hh : IsHomeomorph e := isHomeomorph_iff_continuous_bijective.mpr ⟨hc, e.bijective⟩
  exact IsModuleTopology.iso
    ({ toLinearEquiv := e
       continuous_toFun := hc
       continuous_invFun := (e.isHomeomorph_iff.mp hh).2 } : ULift.{0} M ≃L[R] M)

namespace CurvePlaceIntegralTopology

/-- The original completed valuation subring has its inherited topological ring structure. -/
scoped instance completedIntegerTopologicalRing {k F : Type u} [Field k] [Field F]
    [Algebra k F] (v : AlgebraicCurve.Place k F) :
    IsTopologicalRing (curvePlaceCompletionIntegers v) :=
  inferInstanceAs (IsTopologicalRing (curvePlaceCompletionIntegers v).toSubring)

/-- Actual completed integer rings have open units and their original inversion topology. -/
scoped instance completedIntegerOpenUnits {k F : Type u} [Field k] [Field F]
    [Algebra k F] (v : AlgebraicCurve.Place k F) :
    IsOpenUnits (curvePlaceCompletionIntegers v) :=
  isOpenUnits_openSubring (curvePlaceCompletionIntegers v).toSubring
    (Valued.isOpen_valuationSubring (curvePlaceCompletion v))

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [FiniteDimensional K L] [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [IsScalarTower k K L]
  (p : AlgebraicCurve.Place k K) (q : CurvePlacesAbove k L p)

/-- The actual upper completed integer ring is finite over the lower one. -/
scoped instance localFinite :
    Module.Finite (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers q.1) := by
  let : Module.Finite (curvePlaceCompletionIntegers p)
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletionIntegers q.1) :=
    Module.Finite.equiv (CurvePlaceIntegralTensor.integralTensorEquiv p).toLinearEquiv
  let f : (∀ q : CurvePlacesAbove k L p, curvePlaceCompletionIntegers q.1) →ₗ[
      curvePlaceCompletionIntegers p] curvePlaceCompletionIntegers q.1 := LinearMap.proj q
  exact Module.Finite.of_surjective f (Function.surjective_eval q)

/-- The original completed-integer action is continuous. -/
scoped instance continuousSMul :
    ContinuousSMul (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers q.1) where
  continuous_smul :=
    ((CurvePlaceCompletedIntegersExtension.continuous_completionIntegersMap p q).comp
      continuous_fst).mul continuous_snd

/-- The topology on each original upper integer ring is the finite-module topology. -/
scoped instance moduleTopology :
    IsModuleTopology (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers q.1) := by
  let : CompactSpace (curvePlaceCompletionIntegers p) :=
    curvePlaceCompletionIntegers_compactSpace k K p
  exact compactFiniteModuleIsModuleTopology (curvePlaceCompletionIntegers p)
    (curvePlaceCompletionIntegers q.1)

/-- The finite extension of actual completed integer rings is projective. -/
scoped instance localProjective :
    Module.Projective (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers q.1) := by
  infer_instance

end CurvePlaceIntegralTopology

end Langlands.Global
