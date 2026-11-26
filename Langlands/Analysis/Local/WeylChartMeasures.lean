import Langlands.Analysis.Local.WeylChartMaps
import Langlands.Analysis.Local.UnitsHaarCoordinates

/-! # Additive Haar measure under the product map and the conjugation chart -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory Measure
open scoped NNReal ENNReal

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [ProperSpace F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R] [FiniteDimensional F R] [CompleteSpace R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R]

instance coord_finiteDimensional (γ : Rˣ) : FiniteDimensional F (Coord F γ) := by
  have : FiniteDimensional F ↥(centralizerAlg F γ) :=
    inferInstanceAs (FiniteDimensional F ↥(centralizerAlg F γ).toSubmodule)
  infer_instance

instance coord_properSpace (γ : Rˣ) : ProperSpace (Coord F γ) :=
  FiniteDimensional.proper F (Coord F γ)

instance range_properSpace (γ : Rˣ) : ProperSpace ↥(LinearMap.range (defect F γ)) :=
  FiniteDimensional.proper F _

instance centralizerAlg_properSpace (γ : Rˣ) : ProperSpace ↥(centralizerAlg F γ) :=
  have : FiniteDimensional F ↥(centralizerAlg F γ) :=
    inferInstanceAs (FiniteDimensional F ↥(centralizerAlg F γ).toSubmodule)
  FiniteDimensional.proper F _

/-- Product additive Haar measure on the coordinate space. -/
def coordHaar (γ : Rˣ) : Measure (Coord F γ) :=
  (addHaar : Measure ↥(LinearMap.range (defect F γ))).prod
    (addHaar : Measure ↥(centralizerAlg F γ))

instance coordHaar_isAddHaarMeasure (γ : Rˣ) : (coordHaar (F := F) γ).IsAddHaarMeasure := by
  unfold coordHaar
  infer_instance

/-- The product map pushes coordinate Haar measure on small balls to the image of the
coordinate measure in the ring. -/
theorem exists_productMap_pushforward {γ : Rˣ} (hγ : IsRegularPosition F γ) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r ∈ Ioc 0 r₁,
      BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r) ∧
      ((coordHaar γ).restrict (closedBall 0 r)).map (productMap (F := F) γ) =
        ((coordHaar γ).map (coordCLE hγ)).restrict (coordCLE hγ '' closedBall 0 r) := by
  obtain ⟨R₀, hR₀, h⟩ := local_map_restrict_eq_of_hasStrictFDerivAt (coordHaar γ)
    (coordCLE hγ) (hasStrictFDerivAt_productMap hγ)
  refine ⟨R₀, hR₀, fun r hr => ?_⟩
  obtain ⟨hbij, hmap⟩ := h r hr
  rw [productMap_zero, map_zero] at hbij
  refine ⟨hbij, ?_⟩
  rw [hmap, hbij.image_eq]

/-- The conjugation chart pushes coordinate Haar measure on small balls to the image under
its derivative. -/
theorem exists_conjChart_pushforward {γ : Rˣ} (hγ : IsRegularPosition F γ) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r ∈ Ioc 0 r₂,
      BijOn (conjChart (F := F) γ) (closedBall 0 r)
        (chartDerivative hγ '' closedBall ((chartDerivative hγ).symm 1) r) ∧
      ((coordHaar γ).restrict (closedBall 0 r)).map (conjChart (F := F) γ) =
        ((coordHaar γ).map (chartDerivative hγ)).restrict (conjChart (F := F) γ '' closedBall 0 r) := by
  obtain ⟨R₀, hR₀, h⟩ := local_map_restrict_eq_of_hasStrictFDerivAt (coordHaar γ)
    (chartDerivative hγ) (hasStrictFDerivAt_conjChart hγ)
  refine ⟨R₀, hR₀, fun r hr => ?_⟩
  obtain ⟨hbij, hmap⟩ := h r hr
  rw [conjChart_zero] at hbij
  exact ⟨hbij, hmap⟩

end Langlands.Analysis.WeylChart
