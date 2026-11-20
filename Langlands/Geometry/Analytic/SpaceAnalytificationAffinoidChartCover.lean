import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartNeighborhoods
import Langlands.Geometry.Analytic.FibreProductOpenSubsystem
import Langlands.Geometry.Analytic.AtlasTopology.Refinement

/-! # Shared chart covers by affinoid-algebra points -/

noncomputable section

universe u

open CategoryTheory Set Filter
open _root_.AlgebraicGeometry
open scoped Topology

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X₁ X₂ : AlgebraicSpace (Spec (CommRingCat.of K))}

private theorem exists_target_chart_preimage_neighborhood
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {A : SaturatedAtlasPresentation.{u, u, u} K} {B : AffinoidAtlasPresentation.{u, u, u} K}
    {p : PointFamily K X (localizationFunctor.obj (ofSaturation B))}
    (hp : IsAnalytification K X (localizationFunctor.obj (ofSaturation B)) p)
    (hsep : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    (F : A ⟶ ofSaturation B)
    (i : A.presentation.atlas.Index) (z : BanachSpectrum (A.presentation.atlas.algebra i)) :
    ∃ j : B.atlas.saturatedAtlas.Index,
      (fun t => F.baseMap (A.presentation.atlas.chart i t)) ⁻¹'
        range (B.atlas.saturatedAtlas.chart j) ∈ 𝓝 z ∧
      ∀ (R : PresentedAffinoidAlgebra K)
        (m : localizedAffinoidSpectrum R ⟶ localizationFunctor.obj (ofSaturation B)),
        (∀ t, localizedSpaceFunctor.map m t ∈ range (B.atlas.saturatedAtlas.chart j)) →
          ∃ a : RingPoints K X R, affinoidPointHom hp hsep hft R a = m := by
  obtain ⟨j, hj⟩ := F.target_exists i
  let φ := BanachSpectrum.comapContinuous (F.pullback i j hj).toBoundedRingHom
  obtain ⟨k, -, hnk, hk⟩ := exists_affinoidPointHom_neighborhood B hp hsep hft j (φ z)
  refine ⟨k, ?_, hk⟩
  have hn := φ.continuous.continuousAt.preimage_mem_nhds hnk
  apply Filter.mem_of_superset hn
  intro t ht
  change F.baseMap (A.presentation.atlas.chart i t) ∈ range (B.atlas.saturatedAtlas.chart k)
  have ht' : (ofSaturation B).presentation.atlas.chart j (φ t) ∈
      range (B.atlas.saturatedAtlas.chart k) := ht
  exact (F.chart_comm i j hj t) ▸ ht'

private theorem chart_composite_mem
    {A B : SaturatedAtlasPresentation.{u, u, u} K} (F : A ⟶ B)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : F.baseMap '' range (A.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j))
    (t : localizedSpaceFunctor.obj (localizedAffinoidSpectrum (A.presentation.atlas.algebra i))) :
    localizedSpaceFunctor.map
      (localizationFunctor.map (A.smallChartSpectrumInclusion i) ≫ localizationFunctor.map F) t ∈
        range (B.presentation.atlas.chart j) := by
  rw [← Functor.map_comp]
  change F.baseMap ((A.smallChartSpectrumInclusion i).baseMap t) ∈ range (B.presentation.atlas.chart j)
  exact h ⟨_, A.smallChartSpectrumInclusion_mem i t, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem strong_pair_chartCover
    {A : SaturatedAtlasPresentation.{u, u, u} K}
    {B₁ B₂ : AffinoidAtlasPresentation.{u, u, u} K}
    {p₁ : PointFamily K X₁ (localizationFunctor.obj (ofSaturation B₁))}
    {p₂ : PointFamily K X₂ (localizationFunctor.obj (ofSaturation B₂))}
    (hp₁ : IsAnalytification K X₁ (localizationFunctor.obj (ofSaturation B₁)) p₁)
    (hp₂ : IsAnalytification K X₂ (localizationFunctor.obj (ofSaturation B₂)) p₂)
    (hs₁ : IsSeparated X₁) (ht₁ : LocallyOfFiniteTypeOverBase X₁)
    (hs₂ : IsSeparated X₂) (ht₂ : LocallyOfFiniteTypeOverBase X₂)
    (F₁ : A ⟶ ofSaturation B₁) (F₂ : A ⟶ ofSaturation B₂) :
    ∃ I : Set A.presentation.atlas.Index,
      AtlasTopology.LocallyRefines
        (range (fun i : I => range (A.presentation.atlas.chart i.val))) {univ} ∧
      ∀ i : I, let R := A.presentation.atlas.algebra i.val
        ∃ (x₁ : RingPoints K X₁ R) (x₂ : RingPoints K X₂ R),
          affinoidPointHom hp₁ hs₁ ht₁ R x₁ =
            localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫
              localizationFunctor.map F₁ ∧
          affinoidPointHom hp₂ hs₂ ht₂ R x₂ =
            localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫
              localizationFunctor.map F₂ := by
  let a := A.presentation.atlas
  let I : Set a.Index := {i | ∃ (x₁ : RingPoints K X₁ (a.algebra i)) (x₂ : RingPoints K X₂ (a.algebra i)),
    affinoidPointHom hp₁ hs₁ ht₁ (a.algebra i) x₁ =
      localizationFunctor.map (A.smallChartSpectrumInclusion i) ≫ localizationFunctor.map F₁ ∧
    affinoidPointHom hp₂ hs₂ ht₂ (a.algebra i) x₂ =
      localizationFunctor.map (A.smallChartSpectrumInclusion i) ≫ localizationFunctor.map F₂}
  refine ⟨I, ?_, fun i => i.property⟩
  have hrefine : AtlasTopology.LocallyRefines (range (fun i : I => range (a.chart i.val)))
      (range (fun i : a.Index => range (a.chart i))) := by
    rintro _ ⟨i, rfl⟩ _ ⟨z, rfl⟩
    obtain ⟨j₁, hn₁, h₁⟩ := exists_target_chart_preimage_neighborhood hp₁ hs₁ ht₁ F₁ i z
    obtain ⟨j₂, hn₂, h₂⟩ := exists_target_chart_preimage_neighborhood hp₂ hs₂ ht₂ F₂ i z
    obtain ⟨k, hki, hn, hk⟩ := a.exists_subchart_neighborhood A.hasAllLocalDomains i z _
      (inter_mem hn₁ hn₂)
    have hk' : ∀ t ∈ range (a.chart k),
        F₁.baseMap t ∈ range (B₁.atlas.saturatedAtlas.chart j₁) ∧
        F₂.baseMap t ∈ range (B₂.atlas.saturatedAtlas.chart j₂) := by
      intro t ht
      obtain ⟨s, rfl⟩ := hki ht
      exact hk ht
    have hF₁ : F₁.baseMap '' range (a.chart k) ⊆ range (B₁.atlas.saturatedAtlas.chart j₁) := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hk' t ht).1
    have hF₂ : F₂.baseMap '' range (a.chart k) ⊆ range (B₂.atlas.saturatedAtlas.chart j₂) := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hk' t ht).2
    obtain ⟨x₁, hx₁⟩ := h₁ (a.algebra k) _ (chart_composite_mem F₁ k j₁ hF₁)
    obtain ⟨x₂, hx₂⟩ := h₂ (a.algebra k) _ (chart_composite_mem F₂ k j₂ hF₂)
    have hkI : k ∈ I := ⟨x₁, x₂, hx₁, hx₂⟩
    refine ⟨{range (a.chart k)}, finite_singleton _, singleton_subset_iff.mpr ⟨⟨k, hkI⟩, rfl⟩,
      ?_, ?_⟩
    · rintro _ rfl
      exact ⟨hki, (show z ∈ a.chart i ⁻¹' range (a.chart k) from mem_of_mem_nhds hn)⟩
    · rwa [sUnion_singleton, ← (a.isEmbedding_chart i).map_nhds_eq]
  have hnet := a.isNet_chartFamily.1.refine hrefine
  intro U hU z _
  obtain rfl := mem_singleton_iff.mp hU
  obtain ⟨σ, hσ, hm, hz, hn⟩ := hnet z
  exact ⟨σ, hσ, hm, fun V hV => ⟨subset_univ _, hz V hV⟩, by simpa only [nhdsWithin_univ] using hn⟩

private theorem affinoidPointHom_comp_iso
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y Y' : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p)
    (hs : IsSeparated X) (ht : LocallyOfFiniteTypeOverBase X) (e : Y' ≅ Y)
    (R : PresentedAffinoidAlgebra K) (x : RingPoints K X R) :
    affinoidPointHom (hp.comp_iso e.symm) hs ht R x ≫ e.hom = affinoidPointHom hp hs ht R x := by
  have hc := affinoidPointHom_comp (hp.comp_iso e.symm) hs ht hp hs ht (𝟙 X) e.hom
    (fun A _ _ P y => by
      change (p A P y ≫ e.inv) ≫ e.hom = p A P (RingPoints.map (𝟙 X) y)
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, RingPoints.map_id]) R x
  exact hc.trans (congrArg (affinoidPointHom hp hs ht R) (RingPoints.map_id x))

/-- Two localized maps into analytifications have a common chart cover
on which both are maps of affinoid-algebra points, after changing the
source by an isomorphism. -/
def AffinoidPointHomPairChartCoverStatement
    {Y₁ Y₂ : LocalizedCategory.{u, u, u} (K := K)}
    {p₁ : PointFamily K X₁ Y₁} {p₂ : PointFamily K X₂ Y₂}
    (hp₁ : IsAnalytification K X₁ Y₁ p₁) (hp₂ : IsAnalytification K X₂ Y₂ p₂)
    (hs₁ : IsSeparated X₁) (ht₁ : LocallyOfFiniteTypeOverBase X₁)
    (hs₂ : IsSeparated X₂) (ht₂ : LocallyOfFiniteTypeOverBase X₂) : Prop :=
  ∀ (S : SaturatedAtlasPresentation.{u, u, u} K)
    (f₁ : localizationFunctor.obj S ⟶ Y₁) (f₂ : localizationFunctor.obj S ⟶ Y₂),
    ∃ (A : SaturatedAtlasPresentation.{u, u, u} K)
      (e : localizationFunctor.obj A ≅ localizationFunctor.obj S)
      (I : Set A.presentation.atlas.Index),
      AtlasTopology.LocallyRefines
        (range (fun i : I => range (A.presentation.atlas.chart i.val))) {univ} ∧
      ∀ i : I, let R := A.presentation.atlas.algebra i.val
        ∃ (x₁ : RingPoints K X₁ R) (x₂ : RingPoints K X₂ R),
          affinoidPointHom hp₁ hs₁ ht₁ R x₁ =
            localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom ≫ f₁ ∧
          affinoidPointHom hp₂ hs₂ ht₂ R x₂ =
            localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom ≫ f₂

set_option backward.isDefEq.respectTransparency false in
theorem exists_affinoidPointHom_pair_chartCover
    {Y₁ Y₂ : LocalizedCategory.{u, u, u} (K := K)}
    {p₁ : PointFamily K X₁ Y₁} {p₂ : PointFamily K X₂ Y₂}
    (hp₁ : IsAnalytification K X₁ Y₁ p₁) (hp₂ : IsAnalytification K X₂ Y₂ p₂)
    (hs₁ : IsSeparated X₁) (ht₁ : LocallyOfFiniteTypeOverBase X₁)
    (hs₂ : IsSeparated X₂) (ht₂ : LocallyOfFiniteTypeOverBase X₂) :
    AffinoidPointHomPairChartCoverStatement hp₁ hp₂ hs₁ ht₁ hs₂ ht₂ := by
  intro S f₁ f₂
  obtain ⟨Y₁₀, hY₁⟩ := localizedObjectEquiv.surjective Y₁
  obtain ⟨Y₂₀, hY₂⟩ := localizedObjectEquiv.surjective Y₂
  change localizationFunctor.obj Y₁₀ = Y₁ at hY₁
  change localizationFunctor.obj Y₂₀ = Y₂ at hY₂
  subst Y₁ Y₂
  let e₁ := localizationFunctor.mapIso Y₁₀.saturationIso
  let e₂ := localizationFunctor.mapIso Y₂₀.saturationIso
  obtain ⟨A, s, hs, F₁, F₂, hF₁, hF₂⟩ :=
    exists_commonStrongNumerators (f₁ ≫ e₁.inv) (f₂ ≫ e₂.inv)
  let e := localizedQuasiIso s hs
  obtain ⟨I, hI, h⟩ := strong_pair_chartCover (hp₁.comp_iso e₁.symm) (hp₂.comp_iso e₂.symm)
    hs₁ ht₁ hs₂ ht₂ F₁ F₂
  refine ⟨A, e, I, hI, ?_⟩
  intro i
  obtain ⟨x₁, x₂, hx₁, hx₂⟩ := h i
  refine ⟨x₁, x₂, ?_, ?_⟩
  · rw [← affinoidPointHom_comp_iso hp₁ hs₁ ht₁ e₁, hx₁, Category.assoc,
      ← hF₁, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  · rw [← affinoidPointHom_comp_iso hp₂ hs₂ ht₂ e₂, hx₂, Category.assoc,
      ← hF₂, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

end Langlands.Analytic.SpaceAnalytification
