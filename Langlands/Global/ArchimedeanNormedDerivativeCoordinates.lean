import Langlands.Global.ArchimedeanSmoothTopology
import Langlands.Analysis.CompactRestrictionCoordinates
import Langlands.Analysis.ProductCoordinateScalarization

/-! # Normed coordinates for the actual derivative topology -/

noncomputable section
universe u v
open scoped Topology
open Filter Topology TopologicalSpace
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL
namespace DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A genuine enveloping derivative restricted to a compact set. -/
def normedDerivativeCoordinates : DerivativeSmoothFunctions K n →L[ℝ]
    (∀ i : EnvelopingAlgebra K n × Compacts (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)), C(i.2, ℂ)) :=
  ContinuousLinearMap.pi fun i =>
    ((ContinuousLinearMap.proj i.2).comp
      (Langlands.Analysis.compactRestrictionCoordinates (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) ℂ)).comp
        ((derivativeCLM K n i.1).restrictScalars ℝ)

@[simp]
theorem normedDerivativeCoordinates_apply (f : DerivativeSmoothFunctions K n)
    (a : EnvelopingAlgebra K n) (s : Compacts (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))) (x : s) :
    normedDerivativeCoordinates K n f (a, s) x =
      (envelopingAction K n a (toSmooth K n f)).val x := rfl

theorem tendsto_normedDerivativeCoordinates_iff
    {ι : Type*} {l : Filter ι} {f : ι → DerivativeSmoothFunctions K n}
    {g : DerivativeSmoothFunctions K n} :
    Tendsto (fun i => normedDerivativeCoordinates K n (f i)) l
      (𝓝 (normedDerivativeCoordinates K n g)) ↔ Tendsto f l (𝓝 g) := by
  rw [tendsto_pi_nhds, tendsto_iff_derivativeCoordinates]
  constructor
  · intro h a
    apply (Langlands.Analysis.tendsto_compactRestrictionCoordinates_iff
      (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) ℂ).mp
    rw [tendsto_pi_nhds]
    intro s
    exact h (a, s)
  · intro h i
    have hh := (Langlands.Analysis.tendsto_compactRestrictionCoordinates_iff
      (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) ℂ).mpr (h i.1)
    exact (tendsto_pi_nhds.mp hh) i.2

/-- The actual derivative topology embeds linearly in normed compact
restriction coordinates, without choosing a norm on smooth functions. -/
theorem isEmbedding_normedDerivativeCoordinates :
    IsEmbedding (normedDerivativeCoordinates K n) := by
  refine ⟨isInducing_iff_nhds.mpr (fun f => le_antisymm ?_ ?_), ?_⟩
  · exact (normedDerivativeCoordinates K n).continuous.continuousAt.le_comap
  · exact (tendsto_normedDerivativeCoordinates_iff K n).mp tendsto_comap
  · intro f g h
    apply derivativeCoordinates_injective K n
    funext a
    apply (Langlands.Analysis.isEmbedding_compactRestrictionCoordinates
      (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) ℂ).injective
    funext s
    exact congrArg (fun q => q (a, s)) h

/-- Smoothness of every normed derivative coordinate implies scalar smoothness
after any continuous complex linear functional. -/
theorem contDiffOn_scalar_of_normedDerivativeCoordinates
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    {f : E → DerivativeSmoothFunctions K n} {s : Set E} {m : WithTop ℕ∞}
    (hf : ∀ i, ContDiffOn ℝ m (fun x => normedDerivativeCoordinates K n (f x) i) s) :
    ContDiffOn ℝ m (fun x => ℓ (f x)) s :=
  Langlands.Analysis.contDiffOn_scalar_of_product_embedding
    (normedDerivativeCoordinates K n) (isEmbedding_normedDerivativeCoordinates K n)
    (ℓ.restrictScalars ℝ) hf

end DerivativeSmoothFunctions
end Langlands.Global.ArchimedeanGL
