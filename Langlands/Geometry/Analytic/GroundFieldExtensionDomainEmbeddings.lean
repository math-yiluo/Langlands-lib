import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension
import Langlands.Geometry.Analytic.LocalizedSigmaComponents
import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality

/-! # Domain embeddings under ground field extension -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open _root_.CategoryTheory Set Topology PresentedAffinoidAlgebra
open IndexedAffinoidAtlas.GroundFieldExtension
open PresentedAffinoidAlgebra.GroundFieldExtension (spectrumProjection domainPreservation comap_injective_of_represents represents_range)

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

section Strong

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A B) (hf : f.toStrongHom.IsDomainEmbedding)

local notation "AL" => presentation K L A.atlas
local notation "BL" => presentation K L B.atlas
local notation "g" => CompatibleStrongHom.toStrongHom (compatibleMap K L f)
local notation "pA" => projection K L A.atlas
local notation "pB" => projection K L B.atlas

include hf in
private theorem extendedPullback_represents (i : A.atlas.Index) (j : B.atlas.Index)
    (h : (g).baseMap '' range ((AL).atlas.chart i) ⊆ range ((BL).atlas.chart j)) :
    Represents L ((g).pullback i j h)
      (spectrumProjection K L (B.atlas.algebra j) ⁻¹' f.toStrongHom.chartImageLocus i j) :=
  domainPreservation K L _ _ _ _
    (hf.2 i j ((admissible_iff K L f.toStrongHom f.compatible i j).mp h))

include hf in
/-- The image of an extended source chart is the projection preimage of
its original image. -/
theorem compatibleMap_image_chart (i : A.atlas.Index) :
    (g).baseMap '' range ((AL).atlas.chart i) = pB ⁻¹' (f.baseMap '' range (A.atlas.chart i)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := projection_pointMap K L f.toStrongHom f.compatible x
    change x ∈ range ((chartSystem K L A.atlas).chart i) at hx
    rw [range_chart] at hx
    exact ⟨pA x, hx, h.symm⟩
  · intro hz
    obtain ⟨j, hj⟩ := f.target_exists i
    let hL := (admissible_iff K L f.toStrongHom f.compatible i j).mpr hj
    have hzj : z ∈ range ((BL).atlas.chart j) := (range_chart K L B.atlas j).symm ▸ hj hz
    obtain ⟨t, rfl⟩ := hzj
    have ht : t ∈ range (BanachSpectrum.comap ((g).pullback i j hL).toBoundedRingHom) := by
      rw [(extendedPullback_represents K L f hf i j hL).2.1]
      have hz' : pB ((chartSystem K L B.atlas).chart j t) ∈ f.baseMap ''
          range (A.atlas.chart i) := hz
      change B.atlas.chart j (spectrumProjection K L (B.atlas.algebra j) t) ∈
        f.baseMap '' range (A.atlas.chart i)
      exact (projection_chart K L B.atlas j t) ▸ hz'
    obtain ⟨s, hs⟩ := ht
    exact ⟨(AL).atlas.chart i s, ⟨s, rfl⟩,
      ((g).chart_comm i j hL s).symm.trans (congrArg ((BL).atlas.chart j) hs)⟩

include hf in
/-- The image of a strong domain embedding after ground field extension is
the inverse image of the original domain. -/
theorem compatibleMap_range_domainEmbedding : range (g).baseMap = pB ⁻¹' range f.baseMap := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨pA x, (projection_pointMap K L f.toStrongHom f.compatible x).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨i, hi, hxi⟩ := mem_sUnion.mp (A.atlas.isNet_chartFamily.1.covers.symm ▸ mem_univ x)
    obtain ⟨i, rfl⟩ := hi
    have hz : z ∈ pB ⁻¹' (f.baseMap '' range (A.atlas.chart i)) := ⟨x, hxi, hx⟩
    rw [← compatibleMap_image_chart K L f hf i] at hz
    obtain ⟨y, _, hy⟩ := hz
    exact ⟨y, hy⟩

include hf in
private theorem isEmbedding_comp_extendedChart (i : A.atlas.Index) :
    IsEmbedding ((g).baseMap ∘ (AL).atlas.chart i) := by
  obtain ⟨j, hj⟩ := (g).target_exists i
  have hinj := comap_injective_of_represents (extendedPullback_represents K L f hf i j hj)
  have hc := (BanachSpectrum.comapContinuous ((g).pullback i j hj).toBoundedRingHom).continuous
  have he := ((BL).atlas.isEmbedding_chart j).comp (hc.isClosedEmbedding hinj).isEmbedding
  have hcomp : (BL).atlas.chart j ∘ BanachSpectrum.comap ((g).pullback i j hj).toBoundedRingHom =
      (g).baseMap ∘ (AL).atlas.chart i := funext ((g).chart_comm i j hj)
  exact hcomp ▸ he

include hf in
/-- Scalar extension preserves domain embeddings, with their original full
bounded pullbacks. The image topology is checked on the pulled-back quasinet. -/
theorem compatibleMap_isDomainEmbedding : (g).IsDomainEmbedding := by
  have hnat (x : (AL).space) : pB ((g).baseMap x) = f.baseMap (pA x) :=
    projection_pointMap K L f.toStrongHom f.compatible x
  have hemb i := isEmbedding_comp_extendedChart K L f hf i
  have hinj : Function.Injective (g).baseMap := by
    intro x y hxy
    have hproj := hf.1.injective ((hnat x).symm.trans ((congrArg pB hxy).trans (hnat y)))
    obtain ⟨i, s, rfl⟩ := (chartSystem K L A.atlas).exists_chart x
    have hx : pA ((AL).atlas.chart i s) ∈ range (A.atlas.chart i) := by
      change (AL).atlas.chart i s ∈ pA ⁻¹' range (A.atlas.chart i)
      rw [← range_chart K L A.atlas i]
      exact mem_range_self s
    have hy : y ∈ range ((AL).atlas.chart i) :=
      (range_chart K L A.atlas i).symm ▸ (show pA y ∈ range (A.atlas.chart i) from hproj ▸ hx)
    obtain ⟨t, rfl⟩ := hy
    exact congrArg ((AL).atlas.chart i) ((hemb i).injective hxy)
  let e : (AL).space ≃ range (g).baseMap := Equiv.ofInjective (g).baseMap hinj
  let q : range (g).baseMap → A.space := fun z => pA (e.symm z)
  have hq : Continuous q := by
    apply hf.1.isInducing.continuous_iff.mpr
    have h : f.baseMap ∘ q = pB ∘ Subtype.val := by
      funext z
      exact (hnat (e.symm z)).symm.trans
        (congrArg (fun x : range (g).baseMap => pB x.val) (e.apply_symm_apply z))
    rw [h]
    exact (continuous_projection K L B.atlas).comp continuous_subtype_val
  have hInv : Continuous e.symm := by
    apply (A.atlas.isNet_chartFamily.1.preimage_image hq).continuous
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hset : q ⁻¹' range (A.atlas.chart i) = range (e ∘ (AL).atlas.chart i) := by
      ext z
      change e.symm z ∈ pA ⁻¹' range (A.atlas.chart i) ↔ _
      rw [← range_chart K L A.atlas i]
      constructor
      · rintro ⟨s, hs⟩
        exact ⟨s, (congrArg e hs).trans (e.apply_symm_apply z)⟩
      · rintro ⟨s, rfl⟩
        exact ⟨s, (e.symm_apply_apply _).symm⟩
    rw [hset, continuousOn_iff_continuous_domRestrict]
    have hi : IsEmbedding (e ∘ (AL).atlas.chart i) :=
      IsEmbedding.subtypeVal.of_comp_iff.mp (hemb i)
    let eᵢ := hi.toHomeomorph
    have heq : (range (e ∘ (AL).atlas.chart i)).domRestrict e.symm = (AL).atlas.chart i ∘ eᵢ.symm := by
      funext z
      apply e.injective
      rw [Set.domRestrict_apply, e.apply_symm_apply]
      exact (congrArg Subtype.val (eᵢ.apply_symm_apply z)).symm
    rw [heq]
    exact ((AL).atlas.isEmbedding_chart i).continuous.comp eᵢ.symm.continuous
  let E : (AL).space ≃ₜ range (g).baseMap :=
    { e with continuous_toFun := (g).baseMap.continuous.subtype_mk _, continuous_invFun := hInv }
  refine ⟨IsEmbedding.subtypeVal.comp E.isEmbedding, ?_⟩
  intro i j h
  rw [← (g).range_pullback i j h]
  exact represents_range (extendedPullback_represents K L f hf i j h)

end Strong

section LocalizedCharts

open SaturatedAtlasPresentation

variable (S : SaturatedAtlasPresentation.{u, v, w} K) (i : S.presentation.atlas.Index)

/-- The chart indexed by `i` after extending the actual algebra and
passing to the constructed saturation. -/
abbrev extendedChartIndex : (IndexedAffinoidAtlas.GroundFieldExtension.atlas K L S.presentation.atlas).saturatedAtlas.Index :=
  (IndexedAffinoidAtlas.GroundFieldExtension.atlas K L S.presentation.atlas).originalSaturatedIndex i

private abbrev chartSource : SaturatedAtlasPresentation.{u, v, w} K := S.domain (S.chartDomain i)

private abbrev extendedTarget : SaturatedAtlasPresentation.{u', max u' w, max u' w} L :=
  ofSaturation (IndexedAffinoidAtlas.GroundFieldExtension.presentation K L S.presentation.atlas)

private abbrev extendedSource : SaturatedAtlasPresentation.{u', max u' w, max u' w} L :=
  ofSaturation (IndexedAffinoidAtlas.GroundFieldExtension.presentation K L
    (chartSource K S i).presentation.atlas)

private def extendedInclusion : extendedSource K L S i ⟶ extendedTarget K L S :=
  (compatibleMap K L ((SaturatedAtlasPresentation.compatibleFunctor (K := K)).map
    (S.domainInclusion (S.chartDomain i)))).saturationExtension

private theorem extendedInclusion_isDomainEmbedding : (extendedInclusion K L S i).IsDomainEmbedding := by
  let f := (SaturatedAtlasPresentation.compatibleFunctor (K := K)).map (S.domainInclusion (S.chartDomain i))
  let g := compatibleMap K L f
  have hf : f.toStrongHom.IsDomainEmbedding := S.domainInclusion_isDomainEmbedding (S.chartDomain i)
  exact (compatibleMap_isDomainEmbedding K L f hf).saturationExtension g.coherent

private theorem range_extendedInclusion : range (extendedInclusion K L S i).baseMap =
    range ((extendedTarget K L S).presentation.atlas.chart (extendedChartIndex K L S i)) := by
  let f := (SaturatedAtlasPresentation.compatibleFunctor (K := K)).map (S.domainInclusion (S.chartDomain i))
  have hf : f.toStrongHom.IsDomainEmbedding := S.domainInclusion_isDomainEmbedding (S.chartDomain i)
  refine (compatibleMap_range_domainEmbedding K L f hf).trans ?_
  change projection K L S.presentation.atlas ⁻¹' range (S.domainInclusion (S.chartDomain i)).baseMap = _
  rw [S.range_domainInclusion_baseMap, chartDomain_carrier]
  exact (range_chart K L S.presentation.atlas i).symm.trans
    ((IndexedAffinoidAtlas.GroundFieldExtension.atlas K L S.presentation.atlas).saturatedAtlas_original_range i).symm

local notation "Dₗ" => chartDomain (extendedTarget K L S) (extendedChartIndex K L S i)

private theorem extendedInclusion_mem (x : (extendedSource K L S i).presentation.space) :
    (extendedInclusion K L S i).baseMap x ∈ Dₗ := by
  change (extendedInclusion K L S i).baseMap x ∈ range ((extendedTarget K L S).presentation.atlas.chart _)
  rw [← range_extendedInclusion K L S i]
  exact mem_range_self x

/-- The scalar extension of a chart-domain object is the actual extended
affinoid domain in the scalar-extended analytic space. -/
def extendedChartDomainIso :
    (localizedFunctor K L).obj (localizationFunctor.obj (chartSource K S i)) ≅
      localizationFunctor.obj ((extendedTarget K L S).domain Dₗ) := by
  let t := extendedInclusion K L S i
  let h := extendedInclusion_mem K L S i
  let P := domainSourceSelection t Dₗ h
  have ht := isQuasiIso_domainFactor t (extendedInclusion_isDomainEmbedding K L S i) Dₗ h
    (fun y hy => by
      change y ∈ range (extendedInclusion K L S i).baseMap
      rw [range_extendedInclusion K L S i]
      exact hy)
  let u := (extendedSource K L S i).refiningSubatlasInclusion P
  exact (localizedQuasiIso u (isQuasiIso_refiningSubatlasInclusion P)).symm ≪≫
    localizedQuasiIso (domainFactor t Dₗ h) ht

/-- The comparison identifies the actual image of the original chart inclusion. -/
theorem extendedChartDomainIso_hom_inclusion :
    (extendedChartDomainIso K L S i).hom ≫ (extendedTarget K L S).localizedDomainInclusion Dₗ =
      (localizedFunctor K L).map (S.localizedDomainInclusion (S.chartDomain i)) := by
  let t := extendedInclusion K L S i
  let h := extendedInclusion_mem K L S i
  let P := domainSourceSelection t Dₗ h
  let u := (extendedSource K L S i).refiningSubatlasInclusion P
  let e := localizedQuasiIso u (isQuasiIso_refiningSubatlasInclusion P)
  change _ = (localizedFunctor K L).map (localizationFunctor.map (S.domainInclusion (S.chartDomain i)))
  rw [localizedFunctor_map]
  change (e.inv ≫ localizationFunctor.map (domainFactor t Dₗ h)) ≫
      localizationFunctor.map ((extendedTarget K L S).originalDomainInclusion Dₗ) = localizationFunctor.map t
  rw [Category.assoc, ← Functor.map_comp, domainFactor_comp_inclusion t Dₗ h, Functor.map_comp]
  rw [← localizedQuasiIso_hom u (isQuasiIso_refiningSubatlasInclusion P), Iso.inv_hom_id_assoc]

variable {S i} in
/-- The actual localized scalar-extension functor preserves affinoid domain embeddings. -/
theorem isAffinoidDomainEmbedding_localizedFunctor_map
    {V W : LocalizedCategory.{u, v, w} (K := K)} {j : V ⟶ W} (hj : IsAffinoidDomainEmbedding j) :
    IsAffinoidDomainEmbedding ((localizedFunctor K L).map j) := by
  revert j
  obtain ⟨S, rfl⟩ := localizedObjectEquiv.surjective W
  intro j
  change V ⟶ localizationFunctor.obj S at j
  intro hj
  change ∃ (i : S.presentation.atlas.Index)
    (e : V ≅ localizationFunctor.obj (S.domain (S.chartDomain i))),
    j = e.hom ≫ S.localizedDomainInclusion (S.chartDomain i) at hj
  obtain ⟨i, e, h⟩ := hj
  rw [h]
  change IsAffinoidDomainEmbedding ((localizedFunctor K L).map
    (e.hom ≫ S.localizedDomainInclusion (S.chartDomain i)))
  rw [Functor.map_comp, ← extendedChartDomainIso_hom_inclusion K L _ i]
  erw [← Category.assoc]
  exact ((extendedTarget K L S).isAffinoidDomainEmbedding_localizedDomainInclusion
    (extendedChartIndex K L S i)).iso_comp
      ((localizedFunctor K L).mapIso e ≪≫ extendedChartDomainIso K L S i)

end LocalizedCharts

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
