import Langlands.Geometry.Analytic.AnalyticOpenImmersionBaseChange
import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.EtaleDomainTargetCancellation
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods
import Langlands.Geometry.Analytic.QuasiEtaleCompactCharts
import Langlands.Geometry.Analytic.RecognizedDomainSaturationSite
import Mathlib.Topology.Sets.Opens

/-! # Compact source representatives of pointed analytic étale neighborhoods -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory AffinoidAtlasPresentation Set Filter Topology TopologicalSpace
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exists_compactOpenSlice_strong
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (g : ofSaturation A ⟶ ofSaturation B)
    (hg : StrongHom.IsEtaleAllPieces (A := A) (B := B) g)
    (w : A.space) {N : Set A.space} (hN : N ∈ 𝓝 w) :
    ∃ (D : (ofSaturation A).AnalyticDomain) (U : Set B.space),
      IsCompact D.carrier ∧ T2Space D.carrier ∧ w ∈ D.carrier ∧ D.carrier ⊆ N ∧
      IsOpen U ∧ g.baseMap w ∈ U ∧ IsOpen (D.carrier ∩ g.baseMap ⁻¹' U) := by
  obtain ⟨H, hH, hHsep⟩ := A.atlas.locallyHausdorff w
  obtain ⟨V, W, hV, hW, hwV, hVN, hfin⟩ :=
    (hg.isEtale.isQuasifinite w).exists_small (inter_mem hN hH)
  have hwW : g.baseMap w ∈ W := hfin.1 ⟨w, hwV, rfl⟩
  obtain ⟨J, hJ, hJsep⟩ := B.atlas.locallyHausdorff (g.baseMap w)
  let b := B.atlas.saturatedAtlas
  obtain ⟨I, hI, hIW, hI_nhds⟩ :=
    B.atlas.saturatedAtlas_hasAllLocalDomains.exists_finite_chart_nhds_subset b
      (g.baseMap w) (W ∩ J) (inter_mem (hW.mem_nhds hwW) hJ)
  let : Finite I := hI.to_subtype
  let C : Set B.space := ⋃ j : I, range (b.chart j.val)
  have hCJ : C ⊆ J := iUnion_subset fun j => ((hIW j.val j.property).2).trans inter_subset_right
  let : T2Space C := @Topology.IsEmbedding.t2Space _ _ _ _ hJsep _ (Topology.IsEmbedding.inclusion hCJ)
  have hCn : C ∈ 𝓝 (g.baseMap w) := by
    rw [show C = ⋃ j ∈ I, range (b.chart j) from iUnion_subtype _ _]
    exact hI_nhds
  let Cdom : (ofSaturation B).AnalyticDomain :=
    ⟨C, b.isOriginalChartDomain_of_finite_chart_cover C (fun j : I => j.val) rfl⟩
  let gl := localizationFunctor.map g
  let G : A.space → B.space := g.baseMap
  let D := (ofSaturation A).openDomain V hV ⊓ domainPreimage gl Cdom
  have hD : D.carrier = V ∩ G ⁻¹' C := by
    change (V ∩ localizedSpaceFunctor.map gl ⁻¹' C) = _
    rw [show localizedSpaceFunctor.map gl = TopCat.ofHom g.baseMap from localizedSpaceFunctor_map g]
    rfl
  have hcompactChart (j : I) : IsCompact (V ∩ G ⁻¹' range (b.chart j.val)) := by
    let P := b.originalRecognitionIndex j.val
    have hPW : P.locus ⊆ W := ((hIW j.val j.property).2).trans inter_subset_left
    obtain ⟨Q, _, hQ, _⟩ := hfin.2 P hPW
    change Q.locus = V ∩ G ⁻¹' P.locus at hQ
    exact hQ ▸ (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace Q.locus))
  have hDcompact : IsCompact D.carrier := by
    rw [hD]
    change IsCompact (V ∩ G ⁻¹' ⋃ j : I, range (b.chart j.val))
    rw [preimage_iUnion, inter_iUnion]
    exact isCompact_iUnion hcompactChart
  have hDV : (D.carrier : Set A.space) ⊆ V := hD.symm ▸ inter_subset_left
  have hDH : (D.carrier : Set A.space) ⊆ H := hDV.trans (hVN.trans inter_subset_right)
  have hDsep : T2Space (D.carrier : Set A.space) :=
    @Topology.IsEmbedding.t2Space _ _ _ _ hHsep _ (Topology.IsEmbedding.inclusion hDH)
  let U := interior C
  have hwU : g.baseMap w ∈ U := mem_interior_iff_mem_nhds.mpr hCn
  refine ⟨D, U, hDcompact, hDsep, ?_, hDV.trans (hVN.trans inter_subset_left),
    isOpen_interior, hwU, ?_⟩
  · rw [hD]
    exact ⟨hwV, show g.baseMap w ∈ C from interior_subset hwU⟩
  · have heq : (V ∩ G ⁻¹' C) ∩ G ⁻¹' U = V ∩ G ⁻¹' U := by
      rw [inter_assoc, ← preimage_inter, inter_eq_right.mpr (show U ⊆ C from interior_subset)]
    have hopen : IsOpen ((V ∩ G ⁻¹' C) ∩ G ⁻¹' U) := by
      rw [heq]
      exact hV.inter (isOpen_interior.preimage g.baseMap.continuous)
    exact hD.symm ▸ hopen

variable {W X : LocalizedCategory.{u, v, v} (K := K)} {f : W ⟶ X}

/-- Near a point of an étale map there is a compact Hausdorff analytic source
domain, inside any prescribed neighborhood, that is open over some neighborhood
of the image point. -/
def CompactEtaleNeighborhoodStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {W X : LocalizedCategory.{u, v, v} (K := K)} {f : W ⟶ X},
    etale f →
    ∀ (w : localizedSpaceFunctor.obj W) (N : Set (localizedSpaceFunctor.obj W)), N ∈ 𝓝 w →
    ∃ (D : (presentationOf W).AnalyticDomain) (U : Opens (localizedSpaceFunctor.obj X)),
      IsCompactSpace (domainObj W D) ∧ w ∈ D.carrier ∧ D.carrier ⊆ N ∧
      localizedSpaceFunctor.map f w ∈ U ∧
      IsOpen (D.carrier ∩ localizedSpaceFunctor.map f ⁻¹' (U : Set (localizedSpaceFunctor.obj X)))

theorem compactEtaleNeighborhood : CompactEtaleNeighborhoodStatement.{u, v} K := by
  intro W X f hf w N hN
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let W₀ := localizationFunctor.obj (ofSaturation A)
  let X₀ := localizationFunctor.obj (ofSaturation B)
  let a : W₀ ≅ W := Arrow.leftFunc.mapIso e
  let b : X₀ ≅ X := Arrow.rightFunc.mapIso e
  let ATop := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso a)
  let BTop := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso b)
  have hcomm (z : localizedSpaceFunctor.obj W₀) :
      localizedSpaceFunctor.map f (ATop z) = BTop (g.baseMap z) := by
    have h := congrArg (fun m : W₀ ⟶ X => localizedSpaceFunctor.map m z) e.hom.w
    simp only [Functor.map_comp, TopCat.comp_app] at h
    exact h
  let w₀ := ATop.symm w
  let N₀ := ATop ⁻¹' N
  have hN₀ : N₀ ∈ 𝓝 w₀ := ATop.continuous.continuousAt.preimage_mem_nhds (by
    rwa [ATop.apply_symm_apply])
  obtain ⟨D, U, hDc, hDt, hwD, hDN, hU, hwU, hsem⟩ :=
    exists_compactOpenSlice_strong g hg w₀ hN₀
  let D' := domainPreimage a.inv D
  let U' : Opens (localizedSpaceFunctor.obj X) := ⟨BTop.symm ⁻¹' U, hU.preimage BTop.symm.continuous⟩
  let : CompactSpace (localizedSpaceFunctor.obj (domainObj W₀ D)) := isCompact_iff_compactSpace.mp hDc
  let : T2Space (localizedSpaceFunctor.obj (domainObj W₀ D)) := hDt
  let E := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (domainPreimageIso a.symm D))
  have hb (z : localizedSpaceFunctor.obj W) :
      BTop.symm (localizedSpaceFunctor.map f z) = g.baseMap (ATop.symm z) := by
    apply BTop.injective
    rw [BTop.apply_symm_apply, ← hcomm, ATop.apply_symm_apply]
  refine ⟨D', U', ⟨E.symm.compactSpace, E.symm.t2Space⟩, hwD, ?_, ?_, ?_⟩
  · intro z hz
    change localizedSpaceFunctor.obj W at z
    have hz' : ATop (ATop.symm z) ∈ N := hDN hz
    rwa [ATop.apply_symm_apply] at hz'
  · change BTop.symm (localizedSpaceFunctor.map f w) ∈ U
    rw [hb]
    exact hwU
  · have hEq : D'.carrier ∩ localizedSpaceFunctor.map f ⁻¹' (U' : Set (localizedSpaceFunctor.obj X)) =
        ATop.symm ⁻¹' (D.carrier ∩ g.baseMap ⁻¹' U) := by
      ext z
      change ((ATop.symm z ∈ D.carrier) ∧ BTop.symm (localizedSpaceFunctor.map f z) ∈ U) ↔
        ((ATop.symm z ∈ D.carrier) ∧ g.baseMap (ATop.symm z) ∈ U)
      exact and_congr_right fun _ => (congrArg (fun t : B.space => t ∈ U) (hb z)).to_iff
    exact hEq.symm ▸ hsem.preimage ATop.symm.continuous

/-- Over a target open where a source domain cuts out an open subset of the
ambient source, the inverse-image restriction of the domain map is étale. -/
theorem etale_preimageOpenDomainMap_domainι_comp (hf : etale f)
    (D : (presentationOf W).AnalyticDomain) (U : Opens (localizedSpaceFunctor.obj X))
    (hU : IsOpen (D.carrier ∩ localizedSpaceFunctor.map f ⁻¹' (U : Set (localizedSpaceFunctor.obj X)))) :
    etale (preimageOpenDomainMap (domainι W D ≫ f) (U : Set (localizedSpaceFunctor.obj X)) U.isOpen) := by
  let q := domainι W D ≫ f
  let E := preimageOpenDomain q (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  let F := D.subspaceExtend E
  have hF : F.carrier = D.carrier ∩ localizedSpaceFunctor.map f ⁻¹' (U : Set (localizedSpaceFunctor.obj X)) := by
    ext z
    change (∃ y : D.carrier, y ∈ E.carrier ∧ y.val = z) ↔ _
    have hm (y : D.carrier) : y ∈ E.carrier ↔ localizedSpaceFunctor.map f y.val ∈ U := by
      change localizedSpaceFunctor.obj (domainObj W D) at y
      change localizedSpaceFunctor.map q y ∈ U ↔ _
      have h : localizedSpaceFunctor.map q y = localizedSpaceFunctor.map f y.val := by
        change localizedSpaceFunctor.map (domainι W D ≫ f) y = _
        rw [localizedSpaceFunctor.map_comp, TopCat.comp_app, domainι_apply]
      exact (congrArg (fun t : localizedSpaceFunctor.obj X => t ∈ U) h).to_iff
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, (hm y).mp hy⟩
    · rintro ⟨hzD, hzU⟩
      exact ⟨⟨z, hzD⟩, (hm ⟨z, hzD⟩).mpr hzU, rfl⟩
  have hFopen : IsOpen F.carrier := hF.symm ▸ hU
  have hι : etale (domainι W F) := by
    have hEq : F = (presentationOf W).openDomain F.carrier hFopen := by ext x; rfl
    rw [hEq]
    exact etaleOpenDomainStatement W F.carrier hFopen
  let e : domainObj (domainObj W D) E ≅ domainObj W F :=
    domainNestedLocalizationIso (presentationOf W) D E
  have he : e.hom ≫ domainι W F = domainι (domainObj W D) E ≫ domainι W D :=
    domainNestedLocalizationIso_hom_inclusion (presentationOf W) D E
  have hq := preimageOpenDomainMap_comp q (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  apply etale_of_comp_domainι _
  change etale (preimageOpenDomainMap q _ _ ≫ _)
  rw [hq]
  change etale (domainι (domainObj W D) E ≫ (domainι W D ≫ f))
  rw [← Category.assoc, ← he, Category.assoc e.hom (domainι W F) f]
  exact etale_comp (etale_of_isIso e.hom) (etale_comp hι hf)

end Langlands.Analytic.SaturatedAtlasPresentation
