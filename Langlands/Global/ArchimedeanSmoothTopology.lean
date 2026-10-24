import Langlands.Global.ArchimedeanEnvelopingAction
import Mathlib.Topology.ContinuousMap.LocallyConvex

/-! # The derivative compact-open topology on actual archimedean smooth functions -/

noncomputable section
universe u
open scoped Topology
open Filter Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A dedicated copy of the actual smooth functions, with derivative compact-open topology. -/
def DerivativeSmoothFunctions := SmoothFunctions K n

namespace DerivativeSmoothFunctions

instance : AddCommGroup (DerivativeSmoothFunctions K n) :=
  inferInstanceAs (AddCommGroup (SmoothFunctions K n))

instance : Module ℂ (DerivativeSmoothFunctions K n) :=
  inferInstanceAs (Module ℂ (SmoothFunctions K n))

instance : Module ℝ (DerivativeSmoothFunctions K n) :=
  inferInstanceAs (Module ℝ (SmoothFunctions K n))

instance : IsScalarTower ℝ ℂ (DerivativeSmoothFunctions K n) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (SmoothFunctions K n))

/-- Forget the new topology, retaining precisely the published smooth function. -/
def toSmooth : DerivativeSmoothFunctions K n ≃ₗ[ℂ] SmoothFunctions K n :=
  LinearEquiv.refl ℂ (SmoothFunctions K n)

/-- All genuine enveloping derivatives, viewed as continuous functions. -/
def derivativeCoordinates : DerivativeSmoothFunctions K n →ₗ[ℂ]
    (EnvelopingAlgebra K n →
      C(Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K), ℂ)) :=
  LinearMap.pi fun a => (toContinuousMap K n).comp
    ((envelopingAction K n a).comp (toSmooth K n).toLinearMap)

@[simp]
theorem derivativeCoordinates_apply (f : DerivativeSmoothFunctions K n)
    (a : EnvelopingAlgebra K n) :
    derivativeCoordinates K n f a =
      toContinuousMap K n (envelopingAction K n a (toSmooth K n f)) := rfl

@[simp]
theorem derivativeCoordinates_one (f : DerivativeSmoothFunctions K n) :
    derivativeCoordinates K n f 1 = toContinuousMap K n (toSmooth K n f) := by
  simp

theorem derivativeCoordinates_injective : Function.Injective (derivativeCoordinates K n) := by
  intro f g h
  apply (toSmooth K n).injective
  apply toContinuousMap_injective K n
  simpa using congrFun h 1

instance : TopologicalSpace (DerivativeSmoothFunctions K n) :=
  TopologicalSpace.induced (derivativeCoordinates K n) inferInstance

theorem isEmbedding_derivativeCoordinates : IsEmbedding (derivativeCoordinates K n) :=
  Function.Injective.isEmbedding_induced (derivativeCoordinates_injective K n)

instance : IsTopologicalAddGroup (DerivativeSmoothFunctions K n) :=
  (isEmbedding_derivativeCoordinates K n).isInducing.isTopologicalAddGroup
    (derivativeCoordinates K n)

instance : ContinuousSMul ℂ (DerivativeSmoothFunctions K n) :=
  continuousSMul_induced (derivativeCoordinates K n)

instance : ContinuousSMul ℝ (DerivativeSmoothFunctions K n) :=
  continuousSMul_induced ((derivativeCoordinates K n).restrictScalars ℝ)

instance : T2Space (DerivativeSmoothFunctions K n) :=
  (isEmbedding_derivativeCoordinates K n).t2Space

instance : LocallyConvexSpace ℝ (DerivativeSmoothFunctions K n) :=
  LocallyConvexSpace.induced ((derivativeCoordinates K n).restrictScalars ℝ)

/-- The continuous linear map selecting the derivative indexed by `a`. -/
def derivativeCLM (a : EnvelopingAlgebra K n) : DerivativeSmoothFunctions K n →L[ℂ]
    C(Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K), ℂ) where
  toLinearMap := (LinearMap.proj a).comp (derivativeCoordinates K n)
  cont := (continuous_apply a).comp (isEmbedding_derivativeCoordinates K n).continuous

@[simp]
theorem derivativeCLM_apply (a : EnvelopingAlgebra K n) (f : DerivativeSmoothFunctions K n) :
    derivativeCLM K n a f =
      toContinuousMap K n (envelopingAction K n a (toSmooth K n f)) := rfl

/-- The published enveloping operator transported along the canonical linear equivalence. -/
def operator (a : EnvelopingAlgebra K n) :
    DerivativeSmoothFunctions K n →ₗ[ℂ] DerivativeSmoothFunctions K n :=
  (toSmooth K n).symm.toLinearMap.comp
    ((envelopingAction K n a).comp (toSmooth K n).toLinearMap)

@[simp]
theorem toSmooth_operator (a : EnvelopingAlgebra K n) (f : DerivativeSmoothFunctions K n) :
    toSmooth K n (operator K n a f) = envelopingAction K n a (toSmooth K n f) := rfl

/-- Applying `D(a)` reindexes the `b` coordinate to `b*a`. -/
theorem derivativeCoordinates_operator (a b : EnvelopingAlgebra K n)
    (f : DerivativeSmoothFunctions K n) :
    derivativeCoordinates K n (operator K n a f) b =
      derivativeCoordinates K n f (b * a) := by
  simp only [derivativeCoordinates_apply, toSmooth_operator, envelopingAction_mul]

theorem continuous_operator (a : EnvelopingAlgebra K n) : Continuous (operator K n a) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  change Continuous (fun f => derivativeCoordinates K n (operator K n a f) b)
  simp_rw [derivativeCoordinates_operator]
  exact (derivativeCLM K n (b * a)).continuous

/-- Every fixed genuine enveloping differential operator is continuous. -/
def operatorCLM (a : EnvelopingAlgebra K n) :
    DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n :=
  ⟨operator K n a, continuous_operator K n a⟩

/-- Faithful continuous inclusion into continuous functions, the unit coordinate. -/
def toContinuousMapCLM : DerivativeSmoothFunctions K n →L[ℂ]
    C(Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K), ℂ) :=
  derivativeCLM K n 1

@[simp]
theorem toContinuousMapCLM_apply (f : DerivativeSmoothFunctions K n) :
    toContinuousMapCLM K n f = toContinuousMap K n (toSmooth K n f) := by
  simp [toContinuousMapCLM]

theorem toContinuousMapCLM_injective : Function.Injective (toContinuousMapCLM K n) := by
  intro f g h
  apply (toSmooth K n).injective
  apply toContinuousMap_injective K n
  simpa using h

/-- Point evaluation is continuous and complex linear. -/
def evalCLM (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    DerivativeSmoothFunctions K n →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ x).comp (toContinuousMapCLM K n)

@[simp]
theorem evalCLM_apply
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : DerivativeSmoothFunctions K n) :
    evalCLM K n x f = (toSmooth K n f).val x := by
  simp [evalCLM, ContinuousLinearMap.comp_apply, toContinuousMap]

/-- Convergence is exactly convergence of every derivative in the compact-open topology. -/
theorem tendsto_iff_derivativeCoordinates {ι : Type*} {l : Filter ι}
    {F : ι → DerivativeSmoothFunctions K n} {f : DerivativeSmoothFunctions K n} :
    Tendsto F l (𝓝 f) ↔ ∀ a, Tendsto (fun i => derivativeCoordinates K n (F i) a) l
      (𝓝 (derivativeCoordinates K n f a)) := by
  rw [(isEmbedding_derivativeCoordinates K n).tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- Convergence means uniform convergence on each compact set of each genuine derivative. -/
theorem tendsto_iff_uniformOn_compact {ι : Type*} {l : Filter ι}
    {F : ι → DerivativeSmoothFunctions K n} {f : DerivativeSmoothFunctions K n} :
    Tendsto F l (𝓝 f) ↔ ∀ a, ∀ s : Set
      (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)), IsCompact s →
      TendstoUniformlyOn (fun i => derivativeCoordinates K n (F i) a)
        (derivativeCoordinates K n f a) l s := by
  rw [tendsto_iff_derivativeCoordinates]
  simp only [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]

/-- The neighborhood filter is the infimum of the pulled-back derivative neighborhood filters. -/
theorem nhds_eq_iInf (f : DerivativeSmoothFunctions K n) :
    𝓝 f = ⨅ a : EnvelopingAlgebra K n,
      Filter.comap (fun g => derivativeCoordinates K n g a)
        (𝓝 (derivativeCoordinates K n f a)) := by
  rw [(isEmbedding_derivativeCoordinates K n).isInducing.nhds_eq_comap, nhds_pi,
    Filter.pi, Filter.comap_iInf]
  simp only [Filter.comap_comap, Function.comp_def]

end DerivativeSmoothFunctions
end Langlands.Global.ArchimedeanGL
