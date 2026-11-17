import Langlands.Geometry.Analytic.FieldPointRepresentativeNaturality

/-! # Faithful representatives over prescribed small chart spectra -/

noncomputable section

universe u v uL

namespace Langlands.Analytic

open Set CategoryTheory PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace SaturatedAtlasPresentation

/-- The actual spectrum of a chart, in its presentation's space universe. -/
def smallChartSpectrum (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) : SaturatedAtlasPresentation.{u, v, v} K :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  SmallAffinoidSpectrum.saturated (A.presentation.atlas.algebra i)

/-- The identity on the actual chart algebra induces its strong inclusion. -/
def smallChartSpectrumInclusion (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) : A.smallChartSpectrum i ⟶ A :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  SmallAffinoidSpectrum.chartMap (A.presentation.atlas.algebra i) i
    (BoundedAlgHom.id K (A.presentation.atlas.algebra i))

/-- Every point of the small chart spectrum maps into that actual chart. -/
theorem smallChartSpectrumInclusion_mem (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) (x : (A.smallChartSpectrum i).presentation.space) :
    (A.smallChartSpectrumInclusion i).baseMap x ∈
      range (A.presentation.atlas.chart i) := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  exact SmallAffinoidSpectrum.chartMap_admissible (A.presentation.atlas.algebra i) i _
    (SmallAffinoidSpectrum.globalIndex (A.presentation.atlas.algebra i))
    ⟨x, (SmallAffinoidSpectrum.globalRange (A.presentation.atlas.algebra i)).symm ▸
      mem_univ x, rfl⟩

end SaturatedAtlasPresentation

namespace AffinoidAtlasPresentation.FieldPoint

open PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {P A B : SaturatedAtlasPresentation.{u, v, v} K}

/-- The full field point on the small spectrum of a containing chart,
defined by its actual bounded evaluation. -/
def smallChartPoint (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation) (i : A.presentation.atlas.Index)
    (hi : p.point ∈ range (A.presentation.atlas.chart i)) :
    FieldPoint L (A.smallChartSpectrum i).presentation :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  SmallAffinoidSpectrum.fieldPoint (A.presentation.atlas.algebra i) hd (p.boundedEval i hi)

/-- The small chart inclusion carries its full evaluation point to the
original full point, including every other chart evaluation. -/
theorem smallChartPoint_inclusion
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation) (i : A.presentation.atlas.Index)
    (hi : p.point ∈ range (A.presentation.atlas.chart i)) :
    (p.smallChartPoint hd i hi).map (A.smallChartSpectrumInclusion i)
      (A.smallChartSpectrum i).hasAllLocalDomains = p := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  exact SmallAffinoidSpectrum.fieldPoint_chartMap _ hd _ p i hi _ (BoundedAlgHom.comp_id _)

/-- The actual target-chart pullback followed by the local faithful quotient. -/
def chartTestPullback (p : FieldPoint L P.presentation) (f : P ⟶ A)
    (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
    (i : A.presentation.atlas.Index)
    (hki : f.baseMap '' range (P.presentation.atlas.chart k) ⊆
      range (A.presentation.atlas.chart i)) :
    BoundedAlgHom K (A.presentation.atlas.algebra i) (algebra (p.boundedEval k hk)) :=
  (PresentedAffinoidAlgebra.FaithfulCharacterQuotient.map (p.boundedEval k hk)).comp
    (f.pullback k i hki)

omit [CompleteSpace L] in
/-- The descended character computes the exact evaluation of the full
image point on the prescribed target chart. -/
theorem character_comp_chartTestPullback (p : FieldPoint L P.presentation) (f : P ⟶ A)
    (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
    (i : A.presentation.atlas.Index)
    (hki : f.baseMap '' range (P.presentation.atlas.chart k) ⊆
      range (A.presentation.atlas.chart i)) :
    (character (p.boundedEval k hk)).comp (p.chartTestPullback f k hk i hki) =
      (p.map f P.hasAllLocalDomains).boundedEval i (hki ⟨p.point, hk, rfl⟩) := by
  apply BoundedAlgHom.ext
  intro a
  change character (p.boundedEval k hk)
    (PresentedAffinoidAlgebra.FaithfulCharacterQuotient.map (p.boundedEval k hk)
      (f.pullback k i hki a)) = _
  rw [character_map]
  exact (congrArg (fun ψ : BoundedAlgHom K (A.presentation.atlas.algebra i) L => ψ a)
    (p.map_boundedEval f P.hasAllLocalDomains i _ k hk hki)).symm

/-- The quotient pullback defines a direct strong map from the faithful
representative to the prescribed small target-chart spectrum. -/
def chartTestToSmallChart (p : FieldPoint L P.presentation) (f : P ⟶ A)
    (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
    (i : A.presentation.atlas.Index)
    (hki : f.baseMap '' range (P.presentation.atlas.chart k) ⊆
      range (A.presentation.atlas.chart i)) :
    p.chartTestSource k hk ⟶ A.smallChartSpectrum i :=
  letI : Small.{v} (BanachSpectrum (P.presentation.atlas.algebra k)) :=
    small_of_injective (P.presentation.atlas.isEmbedding_chart k).injective
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  letI := small_spectrum.{u, v} (p.boundedEval k hk)
  SmallAffinoidSpectrum.map (p.chartTestPullback f k hk i hki)

/-- The direct map carries the entire faithful test point to the small
chart point of the actual full image evaluation. -/
theorem chartTestPoint_toSmallChart
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L P.presentation) (f : P ⟶ A)
    (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
    (i : A.presentation.atlas.Index)
    (hki : f.baseMap '' range (P.presentation.atlas.chart k) ⊆
      range (A.presentation.atlas.chart i)) :
    (p.chartTestPoint hd k hk).map (p.chartTestToSmallChart f k hk i hki)
      (p.chartTestSource k hk).hasAllLocalDomains =
      (p.map f P.hasAllLocalDomains).smallChartPoint hd i (hki ⟨p.point, hk, rfl⟩) := by
  let : Small.{v} (BanachSpectrum (P.presentation.atlas.algebra k)) :=
    small_of_injective (P.presentation.atlas.isEmbedding_chart k).injective
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  let := small_spectrum.{u, v} (p.boundedEval k hk)
  change (SmallAffinoidSpectrum.fieldPoint (algebra (p.boundedEval k hk)) hd _).map
    (SmallAffinoidSpectrum.map (p.chartTestPullback f k hk i hki)) _ =
      SmallAffinoidSpectrum.fieldPoint (A.presentation.atlas.algebra i) hd _
  rw [SmallAffinoidSpectrum.fieldPoint_map, character_comp_chartTestPullback]

set_option maxHeartbeats 800000 in
/-- The direct small-chart factorization commutes over the target as an
equality of complete strong morphisms. -/
theorem chartTestToSmallChart_comp_inclusion
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L P.presentation) (f : P ⟶ A)
    (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
    (i : A.presentation.atlas.Index)
    (hki : f.baseMap '' range (P.presentation.atlas.chart k) ⊆
      range (A.presentation.atlas.chart i)) :
    p.chartTestToSmallChart f k hk i hki ≫ A.smallChartSpectrumInclusion i =
      p.chartTestMap k hk ≫ f := by
  let : Small.{v} (BanachSpectrum (P.presentation.atlas.algebra k)) :=
    small_of_injective (P.presentation.atlas.isEmbedding_chart k).injective
  apply hom_eq_of_common_chart_testPoint_map_eq (p.boundedEval k hk) hd _ _ i
  · intro x
    exact A.smallChartSpectrumInclusion_mem i ((p.chartTestToSmallChart f k hk i hki).baseMap x)
  · intro x
    exact hki ⟨(p.chartTestMap k hk).baseMap x, p.chartTestMap_mem k hk x, rfl⟩
  · change (p.chartTestPoint hd k hk).map
        ((p.chartTestToSmallChart f k hk i hki).saturatedComp
          (A.smallChartSpectrumInclusion i) _ _) _ =
      (p.chartTestPoint hd k hk).map ((p.chartTestMap k hk).saturatedComp f _ _) _
    rw [map_saturatedComp, map_saturatedComp, chartTestPoint_toSmallChart,
      smallChartPoint_inclusion, chartTestPoint_map]

set_option maxHeartbeats 800000 in
/-- One faithful containing-chart representative factors through both
prescribed image-chart spectra, preserving full points and both strong triangles. -/
theorem exists_chartTest_pair_factorization
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L P.presentation) (f : P ⟶ A) (g : P ⟶ B)
    (i : A.presentation.atlas.Index)
    (hi : f.baseMap p.point ∈ range (A.presentation.atlas.chart i))
    (j : B.presentation.atlas.Index)
    (hj : g.baseMap p.point ∈ range (B.presentation.atlas.chart j)) :
    ∃ (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
      (hki : f.baseMap '' range (P.presentation.atlas.chart k) ⊆
        range (A.presentation.atlas.chart i))
      (hkj : g.baseMap '' range (P.presentation.atlas.chart k) ⊆
        range (B.presentation.atlas.chart j)),
      (p.chartTestPoint hd k hk).map (p.chartTestToSmallChart f k hk i hki)
          (p.chartTestSource k hk).hasAllLocalDomains =
        (p.map f P.hasAllLocalDomains).smallChartPoint hd i hi ∧
      (p.chartTestPoint hd k hk).map (p.chartTestToSmallChart g k hk j hkj)
          (p.chartTestSource k hk).hasAllLocalDomains =
        (p.map g P.hasAllLocalDomains).smallChartPoint hd j hj ∧
      p.chartTestToSmallChart f k hk i hki ≫ A.smallChartSpectrumInclusion i =
        p.chartTestMap k hk ≫ f ∧
      p.chartTestToSmallChart g k hk j hkj ≫ B.smallChartSpectrumInclusion j =
        p.chartTestMap k hk ≫ g := by
  obtain ⟨kf, hkf, hf⟩ := f.exists_admissible_mem P.hasAllLocalDomains p.point i hi
  obtain ⟨kg, hkg, hg⟩ := g.exists_admissible_mem P.hasAllLocalDomains p.point j hj
  obtain ⟨k, hsub, hk⟩ := IndexedAffinoidAtlas.exists_chart_inter hkf hkg
  have hki := (image_mono (hsub.trans inter_subset_left)).trans hf
  have hkj := (image_mono (hsub.trans inter_subset_right)).trans hg
  exact ⟨k, hk, hki, hkj, p.chartTestPoint_toSmallChart hd f k hk i hki,
    p.chartTestPoint_toSmallChart hd g k hk j hkj,
    p.chartTestToSmallChart_comp_inclusion hd f k hk i hki,
    p.chartTestToSmallChart_comp_inclusion hd g k hk j hkj⟩

end AffinoidAtlasPresentation.FieldPoint

end Langlands.Analytic
