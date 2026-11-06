import Langlands.Geometry.Analytic.SpecialCoverIntersectionQuotient
import Langlands.Geometry.Analytic.AtlasFiniteProductLocus
import Langlands.Geometry.Analytic.AtlasIntersectionQuotientRecognition
import Langlands.Geometry.Analytic.SpecialSetIntersectionStatement

/-! # Full special-set intersections from ideal effectiveness -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra LocalDomain

namespace FiniteChartGluingData.SubordinateProductIntersection

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {d : FiniteChartGluingData a} {U V : LocalDomain a}
  (cU : d.SubordinateLocalDomainCover U) (cV : d.SubordinateLocalDomainCover V)

/-- Effective local kernels yield full finite recognition data for the actual
closed coproduct quotient, including derived union and saturation. -/
def finiteIntersectionData
    (heffect : Domain.FiniteCover.IdealEffectivenessStatement.{u})
    (hspecial : d.IsSpecialCover) :
    FiniteIntersectionData U V (algebra cU cV)
      ((globalMap cU cV).comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))
      ((globalMap cU cV).comp (AffinoidCoproduct.rightMap K U.algebra V.algebra)) :=
  FiniteIntersectionData.ofFiniteExtendedProductCover
    (globalMap cU cV) cU.algebraCover cV.algebraCover (quotientCover cU cV)
    (cU.algebraCover.productIndexEquiv cV.algebraCover)
    (fun i => (intersection cU cV i).obj)
    (fun i => (intersection cU cV i).left)
    (fun i => (intersection cU cV i).right)
    (localEquiv cU cV heffect hspecial)
    (localEquiv_comp_leftMap cU cV heffect hspecial)
    (localEquiv_comp_rightMap cU cV heffect hspecial)
    (fun i => (intersection cU cV i).locus_eq)
    (fun _ => rfl)

end FiniteChartGluingData.SubordinateProductIntersection

/-- General closed-ideal effectiveness implies the entire published full
special-set intersection proposition, with its independent universes. -/
theorem specialSetIntersection_of_idealEffectiveness
    (heffect : Domain.FiniteCover.IdealEffectivenessStatement.{u}) :
    SpecialSetIntersectionStatement.{u, v, w} := by
  intro K _ _ _ X _ a W hW U V hU hV
  obtain ⟨d, hd, hspecial⟩ := hW
  let : T2Space d.locus := hspecial.1
  let cU := d.subordinateLocalDomainCover U (fun x hx => hd.symm ▸ hU hx)
  let cV := d.subordinateLocalDomainCover V (fun x hx => hd.symm ▸ hV hx)
  exact FiniteIntersectionData.exists_of_admissibleCoproduct
    (FiniteChartGluingData.SubordinateProductIntersection.globalMap cU cV)
    (FiniteChartGluingData.SubordinateProductIntersection.finiteIntersectionData
      cU cV heffect hspecial)
    (FiniteChartGluingData.SubordinateProductIntersection.globalMap_isAdmissibleEpi cU cV)

end Langlands.Analytic.IndexedAffinoidAtlas
