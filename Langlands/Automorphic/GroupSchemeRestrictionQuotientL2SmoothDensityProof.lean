import Langlands.Automorphic.GroupSchemeQuotientL2SmoothDensityProof
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2SmoothDensityStatement

/-! # Transport of smooth density to the restriction split-centre quotient -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped Manifold ContDiff

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.Automorphic.GroupSchemeFunctions

/-- The canonical quotient isometry transports both smooth density statements. -/
theorem quotientL2SmoothDensity : QuotientL2SmoothDensityStatement := by
  classical
  intro F _ _ G _ _ hG S j T i h hi _ hc hT _ hInv
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
  obtain ⟨I, _, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let model := 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension)
  obtain ⟨hSmooth, hBoth⟩ := groupSchemeQuotientL2SmoothDensity F G hG T i hi I e hc
  exact ⟨(dense_smoothVectors_iff F G h hi hc hInv I e model).mpr hSmooth,
    (dense_biSmoothVectors_iff F G h hi hc hInv I e model).mpr hBoth⟩

end Langlands.Global.RestrictionSplitCentre
