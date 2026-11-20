import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartLifts
import Langlands.Geometry.Analytic.SaturatedRecognitionCospans
import Langlands.Geometry.Analytic.FieldPointRepresentativeChartFactorization

/-! # Affinoid point maps on chart neighborhoods -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Set
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SmallAffinoidSpectrum

open SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
private theorem cast_comp_cast {R S R' S' T : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S') (f : BoundedAlgHom K R S)
    (g : BoundedAlgHom K T R) :
    (hS ▸ (hR ▸ f : BoundedAlgHom K R' S) : BoundedAlgHom K R' S').comp
      (hR ▸ g : BoundedAlgHom K T R') = (hS ▸ f.comp g : BoundedAlgHom K T S') := by
  subst R' S'
  rfl

omit [CompleteSpace K] in
private theorem cast_cast_heq {R S R' S' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S') (f : BoundedAlgHom K R S) :
    HEq (hS ▸ (hR ▸ f : BoundedAlgHom K R' S) : BoundedAlgHom K R' S') f := by
  subst R' S'
  rfl

private theorem chartSourceMap_precomp
    {A B C : SaturatedAtlasPresentation.{u, v, v} K}
    (i : A.presentation.atlas.Index) (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index) (hj : range (B.presentation.atlas.chart j) = univ)
    (k : C.presentation.atlas.Index) (F : A ⟶ B)
    (hF : F.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j))
    (g : BoundedAlgHom K (C.presentation.atlas.algebra k) (B.presentation.atlas.algebra j)) :
    F ≫ chartSourceMap j hj k g =
      chartSourceMap i hi k ((F.pullback i j hF).comp g) := by
  have h := chartSourceMap_comp i hi j (F.pullback i j hF) (chartSourceMap j hj k g) k
    (chartSourceMap_admissible j hj k g j)
  rw [chartSourceMap_eq i hi j F hF, chartSourceMap_pullback_global] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition of a chart map retains the complete bounded coefficient map. -/
theorem map_comp_chartMap {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    {B : SaturatedAtlasPresentation.{u, v, v} K} (f : BoundedAlgHom K R S)
    (j : B.presentation.atlas.Index) (g : BoundedAlgHom K (B.presentation.atlas.algebra j) R) :
    map.{u, v} f ≫ chartMap R j g = chartMap S j (f.comp g) := by
  let i := globalIndex.{u, v} R
  let c := globalIndex.{u, v} S
  let gs : BoundedAlgHom K (B.presentation.atlas.algebra j)
      ((saturated R).presentation.atlas.algebra i) := (globalAlgebra R).symm ▸ g
  have hf : (map.{u, v} f).baseMap '' range ((saturated S).presentation.atlas.chart c) ⊆
      range ((saturated R).presentation.atlas.chart i) := by
    rw [show range ((saturated R).presentation.atlas.chart i) = univ from globalRange R]
    exact subset_univ _
  have hpb : (map.{u, v} f).pullback c i hf =
      ((globalAlgebra S).symm ▸ ((globalAlgebra R).symm ▸ f :
        BoundedAlgHom K ((saturated R).presentation.atlas.algebra i) S)) := by
    apply eq_of_heq
    exact (map_pullbackAtTop_heq.{u, v} f).trans
      (cast_cast_heq (globalAlgebra R).symm (globalAlgebra S).symm f).symm
  change map f ≫ chartSourceMap i (globalRange R) j gs =
    chartSourceMap c (globalRange S) j ((globalAlgebra S).symm ▸ f.comp g)
  have hmaps := chartSourceMap_precomp c (globalRange S) i (globalRange R) j (map f) hf gs
  have hcoeff :
      ((map f).pullback c i hf).comp gs = (globalAlgebra S).symm ▸ f.comp g :=
    (congrArg (·.comp gs) hpb).trans
      (cast_comp_cast (globalAlgebra R).symm (globalAlgebra S).symm f g)
  exact hmaps.trans (congrArg (chartSourceMap c (globalRange S) j) hcoeff)

end Langlands.Analytic.SmallAffinoidSpectrum

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation AffineAnalytification
open Filter
open scoped Topology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

private theorem smallChartSpectrumInclusion_comp
    {A B : SaturatedAtlasPresentation.{u, u, u} K} (F : A ⟶ B)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : F.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j)) :
    A.smallChartSpectrumInclusion i ≫ F =
      SmallAffinoidSpectrum.map.{u, u} (F.pullback i j h) ≫ B.smallChartSpectrumInclusion j := by
  let R := A.presentation.atlas.algebra i
  let S := B.presentation.atlas.algebra j
  let g := F.pullback i j h
  have h₁ := SmallAffinoidSpectrum.chartMap_comp R i (BoundedAlgHom.id K R) F j h
  have h₂ := SmallAffinoidSpectrum.map_comp_chartMap.{u, u} g j (BoundedAlgHom.id K S)
  rw [BoundedAlgHom.id_comp] at h₁
  rw [BoundedAlgHom.comp_id] at h₂
  exact h₁.trans h₂.symm

private theorem invert_comparison_square {C : Type*} [Category C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B')
    (F : A ⟶ B) (F' : A' ⟶ B') (h : eA.hom ≫ F' = F ≫ eB.hom) :
    F' ≫ eB.inv = eA.inv ≫ F := by
  apply (cancel_epi eA.hom).mp
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

/-- Each point of a target chart has a subchart neighborhood in that
chart on which every affinoid map comes from a ring-valued point. -/
def AffinoidPointHomChartNeighborhoodStatement
    (B : AffinoidAtlasPresentation.{u, u, u} K)
    {p : PointFamily K X (localizationFunctor.obj (ofSaturation B))}
    (hp : IsAnalytification K X (localizationFunctor.obj (ofSaturation B)) p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X) : Prop :=
  ∀ (j : B.atlas.saturatedAtlas.Index) (z : BanachSpectrum (B.atlas.saturatedAtlas.algebra j)),
    ∃ k : B.atlas.saturatedAtlas.Index,
      range (B.atlas.saturatedAtlas.chart k) ⊆ range (B.atlas.saturatedAtlas.chart j) ∧
      B.atlas.saturatedAtlas.chart j ⁻¹' range (B.atlas.saturatedAtlas.chart k) ∈ 𝓝 z ∧
      ∀ (R : PresentedAffinoidAlgebra K)
        (m : localizedAffinoidSpectrum R ⟶ localizationFunctor.obj (ofSaturation B)),
        (∀ t, localizedSpaceFunctor.map m t ∈ range (B.atlas.saturatedAtlas.chart k)) →
          ∃ a : RingPoints K X R, affinoidPointHom hp hX hft R a = m

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem exists_affinoidPointHom_neighborhood
    (B : AffinoidAtlasPresentation.{u, u, u} K)
    {p : PointFamily K X (localizationFunctor.obj (ofSaturation B))}
    (hp : IsAnalytification K X (localizationFunctor.obj (ofSaturation B)) p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X) :
    AffinoidPointHomChartNeighborhoodStatement B hp hX hft := by
  intro j z
  obtain ⟨A, _, _, Q, x, hx, t, ht⟩ := hp.jointly_surjective (B.atlas.saturatedAtlas.chart j z)
  obtain ⟨A₀, E, r, he, hr⟩ := exists_strongEtale_representative (p A Q x) (hp.etale_map Q x hx)
  let y := localizedSpaceFunctor.map r.inv t
  have hyr : localizedSpaceFunctor.map r.hom y = t :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso r)).apply_symm_apply t
  have hy : B.atlas.saturatedAtlas.chart j z = E.baseMap y := by
    change _ = localizedSpaceFunctor.map (localizationFunctor.map E) y
    rw [← hr, Functor.map_comp, TopCat.comp_app, hyr, ht]
  obtain ⟨k, V, h, -, -, hk, hn, hfin, het, hsurj⟩ :=
    he.exists_surjective_finiteEtalePair y j z hy (N := univ) univ_mem
  let W := B.atlas.saturatedAtlas.originalRecognitionIndex k
  let B' := ofFullRecognition B
  let A' : SaturatedAtlasPresentation.{u, u, u} K :=
    ⟨E.recognitionSource, E.recognitionSource_hasAllLocalDomains⟩
  let E' : A' ⟶ B' := E.recognitionMap
  let aComp : ofSaturation A₀ ⟶ A' := E.recognitionSourceComparison
  let bComp : ofSaturation B ⟶ B' := B.localDomainToFullRecognition
  let eA := localizedQuasiIso aComp E.recognitionSourceComparison_isQuasiIso
  let eB := localizedQuasiIso bComp B.localDomainToFullRecognition_isQuasiIso
  have hE : eA.hom ≫ localizationFunctor.map E' = localizationFunctor.map E ≫ eB.hom := by
    change localizationFunctor.map aComp ≫ localizationFunctor.map E' =
      localizationFunctor.map E ≫ localizationFunctor.map bComp
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg localizationFunctor.map E.recognitionSourceComparison_comp
  let J : A'.presentation.atlas.Index := E.recognitionSourceIndex V W h
  let f := E.fullRecognitionPairs.pullback V W h
  let tD : localizedAffinoidSpectrum W.algebra ⟶ localizationFunctor.obj B' :=
    localizationFunctor.map (B'.smallChartSpectrumInclusion W)
  let tU : localizedAffinoidSpectrum V.algebra ⟶ localizationFunctor.obj A' :=
    localizationFunctor.map (A'.smallChartSpectrumInclusion J)
  let i := tD ≫ eB.inv
  let s := tU ≫ eA.inv ≫ r.hom
  have hchart : tU ≫ localizationFunctor.map E' =
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} f) ≫ tD := by
    change localizationFunctor.map (A'.smallChartSpectrumInclusion J) ≫
      localizationFunctor.map E' =
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} f) ≫
        localizationFunctor.map (B'.smallChartSpectrumInclusion W)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg localizationFunctor.map (smallChartSpectrumInclusion_comp E' J W h)
  have hs : s ≫ p A Q x = localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} f) ≫ i := by
    dsimp only [s, i]
    rw [Category.assoc, Category.assoc, hr,
      ← invert_comparison_square eA eB _ _ hE, ← Category.assoc, hchart, Category.assoc]
  have hW : range (B'.presentation.atlas.chart W) = range (B.atlas.saturatedAtlas.chart k) :=
    B.atlas.saturatedAtlas.recognitionAtlas_original_range k
  have hW' : W.locus = range (B.atlas.saturatedAtlas.chart k) := W.range_chart.symm.trans hW
  refine ⟨k, hW' ▸ hk, hW' ▸ hn, ?_⟩
  intro R m hm
  have hm' (w : localizedSpaceFunctor.obj (localizedAffinoidSpectrum R)) :
      localizedSpaceFunctor.map (m ≫ eB.hom) w ∈ range (B'.presentation.atlas.chart W) := by
    rw [Functor.map_comp, TopCat.comp_app, hW]
    exact hm w
  obtain ⟨g, hg, -⟩ := SmallAffinoidSpectrum.localizedAffinoidChartFactorization
    B' R W (m ≫ eB.hom) hm'
  let D := B'.presentation.atlas.algebra W
  have hmap := SmallAffinoidSpectrum.map_comp_chartMap.{u, u} (B := B') g W (BoundedAlgHom.id K D)
  rw [BoundedAlgHom.comp_id] at hmap
  have hmEq : localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g) ≫ i = m := by
    change localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g) ≫
      localizationFunctor.map (B'.smallChartSpectrumInclusion W) ≫ eB.inv = m
    rw [← Category.assoc, ← Functor.map_comp]
    change localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g ≫
      SmallAffinoidSpectrum.chartMap D W (BoundedAlgHom.id K D)) ≫ eB.inv = m
    rw [hmap, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨a, ha⟩ := exists_affinoidPointHom_of_finite_chart hp hX hft f g hfin het hsurj i Q x s hs
  exact ⟨a, ha.trans hmEq⟩

end Langlands.Analytic.SpaceAnalytification
