import Langlands.Automorphic.GroupSchemeQuotientL2FiniteApproximationProof
import Langlands.Automorphic.GroupSchemeQuotientL2SmoothDensityStatement
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2SmoothVectors
import Langlands.Representation.Unitary.IntegratedIsometricSmoothDensityProof

/-! # Archimedean and simultaneous smooth density on the positive-torus quotient -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj Manifold ContDiff Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- Archimedean smoothing followed by sufficiently small finite subgroup averaging
gives dense simultaneous smooth vectors for the original quotient actions. -/
theorem groupSchemeQuotientL2SmoothDensity : GroupSchemeQuotientL2SmoothDensityStatement.{u} := by
  intro F _ _ G _ _ hG T i hi _ I _ e hc _
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
  let := InfiniteAdelicGroupPoints.reductiveLieGroup F G hG
  let V := InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension
  let μInf : Measure (InfiniteAdelicGroupPoints F G) := Measure.haar
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let πInf := haarQuotientL2InfiniteRightAction F G T i hi I e hc
  let Sm := Langlands.Archimedean.smoothVectors 𝓘(ℝ, V) πInf
  have hDense : Dense (Sm : Set (Lp ℂ 2 μQ)) :=
    integratedIsometricSmoothDensity V (InfiniteAdelicGroupPoints F G) (Lp ℂ 2 μQ) μInf πInf
      (norm_haarQuotientL2InfiniteRightAction F G T i hi I e hc)
      (haarQuotientL2InfiniteOrbit_aestronglyMeasurable F G T i hi I e hc μInf)
      (continuous_haarQuotientL2InfiniteOrbit F G T i hi I e hc)
  refine ⟨hDense, ?_⟩
  obtain ⟨K, hK, _, hFixed, hConverges, _⟩ :=
    groupSchemeQuotientL2FiniteApproximation F G T i hi I e hc
  intro φ
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨ψ, hψ, hDist⟩ := (Metric.mem_closure_iff.mp (hDense φ)) (ε / 2) (half_pos hε)
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp (hConverges ψ) (ε / 2) (half_pos hε)
  let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
  let A := haarQuotientL2FiniteAverage F G T i hi I e hc (K n)
  have hSmooth : A ψ ∈ Sm :=
    RestrictionSplitCentre.isSmoothVector_of_intertwining 𝓘(ℝ, V) πInf πInf A
      (fun a v => (haarQuotientL2FiniteAverage_infiniteRightAction F G T i hi I e hc (K n) a v).symm)
      hψ
  refine ⟨A ψ, ⟨hSmooth, ⟨K n, hFixed n ψ⟩⟩, ?_⟩
  have hClose : dist ψ (A ψ) < ε / 2 := by
    rw [dist_comm]
    exact hn n le_rfl
  calc
    dist φ (A ψ) ≤ dist φ ψ + dist ψ (A ψ) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hDist hClose
    _ = ε := add_halves ε

end Langlands.Automorphic.GroupSchemeFunctions
