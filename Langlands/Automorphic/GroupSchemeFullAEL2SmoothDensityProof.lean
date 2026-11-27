import Langlands.Automorphic.GroupSchemeFullAEL2SmoothDensityStatement
import Langlands.Automorphic.GroupSchemeQuotientL2SmoothDensityProof

/-! # Smooth-vector density in the full cuspidal Hilbert space -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Global.RestrictionSplitCentre

/-- The original orthogonal projection maps the ambient dense smooth families into
the corresponding smooth families in the full cuspidal subspace. -/
theorem groupSchemeFullAEL2SmoothDensity : GroupSchemeFullAEL2SmoothDensityStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
  let model := 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension)
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let C := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let projection : Lp ℂ 2 μQ →L[ℂ] C :=
    fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc
  let πInf := haarQuotientL2InfiniteRightAction F G T i hi I e hc
  let cuspInf : InfiniteAdelicGroupPoints F G →* (C →L[ℂ] C) :=
    fullAEL2CuspidalInfiniteRightAction F G hPD hG T i hi I e hc
  let πFin := haarQuotientL2FiniteRightAction F G T i hi I e hc
  let cuspFin : Representation ℂ (FiniteAdelicGroupPoints F G) C :=
    fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc
  let smoothCusp : Submodule ℂ C :=
    Langlands.Archimedean.smoothVectors (G := InfiniteAdelicGroupPoints F G) model cuspInf
  have hSurj : Function.Surjective projection := fun φ =>
    ⟨φ.val, fullAEL2CuspidalOrthogonalProjection_inclusion F G hPD hG T i hi I e hc φ⟩
  have mapSmooth {φ : Lp ℂ 2 μQ} (hφ : φ ∈ Langlands.Archimedean.smoothVectors model πInf) :
      projection φ ∈ smoothCusp :=
    isSmoothVector_of_intertwining model πInf cuspInf projection
      (fullAEL2CuspidalOrthogonalProjection_infiniteRightAction F G hPD hG T i hi I e hc) hφ
  have mapFinite {φ : Lp ℂ 2 μQ} (hφ : Langlands.IsSmoothVector πFin φ) :
      Langlands.IsSmoothVector cuspFin (projection φ) :=
    isSmoothVector_of_finiteIntertwining πFin cuspFin projection.toLinearMap
      (fun b => fullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG T i hi I e hc
        (ofFinite F G b)) hφ
  obtain ⟨hSmooth, hBoth⟩ := groupSchemeQuotientL2SmoothDensity F G hG T i hi I e hc
  refine ⟨(hSurj.denseRange.dense_image projection.continuous hSmooth).mono ?_,
    (hSurj.denseRange.dense_image projection.continuous hBoth).mono ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact mapSmooth hφ
  · rintro _ ⟨φ, ⟨hφ, hφFin⟩, rfl⟩
    exact ⟨mapSmooth hφ, mapFinite hφFin⟩

end Langlands.Automorphic.GroupSchemeFunctions
