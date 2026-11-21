import Langlands.Geometry.Analytic.FullRecognitionFiniteRightCancellationStatement
import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityProof
import Langlands.Geometry.Analytic.FiniteCommonBaseTriangle

/-! # Finite right cancellation over a common open base -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set Filter
open scoped Topology

/-- Finite right cancellation for actual saturated analytic presentations. -/
theorem finiteOverRightCancellation (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    FiniteOverRightCancellationStatement.{u, v, w} K := by
  intro A B C g g' V U T hV hU hT hVU hg' hcomp
  apply finiteOverTargetLocality.{u, v, w} K A B g V U hV hU hVU
  intro x hxU
  have hxT : g'.baseMap x ∈ T := hg'.1 ⟨x, hxU, rfl⟩
  obtain ⟨I, hIfin, hIT, hIN⟩ := C.atlas.exists_finite_recognized_nhds_subset
    (g'.baseMap x) T (hT.mem_nhds hxT)
  let : Finite I := hIfin.to_subtype
  let triangle := fun Z : I =>
    finiteCommonBaseTriangle hVU hg' hcomp Z.1 (hIT Z.1 Z.2).2
  let middle := fun Z : I => (triangle Z).middle
  let J : Set B.atlas.saturatedAtlas.RecognizedSubset := Set.range middle
  refine ⟨J, Set.finite_range middle, ?_, ?_⟩
  · rintro _ ⟨Z, rfl⟩
    refine ⟨?_, ?_, (triangle Z).source, (triangle Z).sourceToMiddle,
      (triangle Z).source_preimage, (triangle Z).source_finite⟩
    · exact (triangle Z).middle_locus.symm ▸ ⟨hxU, (hIT Z.1 Z.2).1⟩
    · exact (triangle Z).middle_locus.trans_subset Set.inter_subset_left
  · have hN : U ∩ g'.baseMap ⁻¹' (⋃ Z ∈ I, Z.locus) ∈ 𝓝 x :=
      Filter.inter_mem (hU.mem_nhds hxU)
        (g'.baseMap.continuous.continuousAt.preimage_mem_nhds hIN)
    refine Filter.mem_of_superset hN ?_
    rintro y ⟨hyU, hyI⟩
    obtain ⟨Z, hZI, hyZ⟩ := Set.mem_iUnion₂.1 hyI
    exact Set.mem_biUnion (⟨⟨Z, hZI⟩, rfl⟩ : middle ⟨Z, hZI⟩ ∈ J)
      ((triangle ⟨Z, hZI⟩).middle_locus.symm ▸ ⟨hyU, hyZ⟩)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
