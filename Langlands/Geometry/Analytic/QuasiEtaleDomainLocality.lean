import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearPostcomposition
import Langlands.Geometry.Analytic.SaturatedLocalizedIsomorphisms

/-! # Quasi-étale recognition from analytic-domain restrictions -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private def chartDomainIsoOfImage {S T : SaturatedAtlasPresentation.{u, v, v} K}
    (e : localizationFunctor.obj S ≅ localizationFunctor.obj T)
    (i : S.presentation.atlas.Index) (j : T.presentation.atlas.Index)
    (h : range (T.presentation.atlas.chart j) =
      localizedSpaceFunctor.map e.hom '' range (S.presentation.atlas.chart i)) :
    localizationFunctor.obj (S.domain (S.chartDomain i)) ≅
      localizationFunctor.obj (T.domain (T.chartDomain j)) :=
  domainRestrictIso e (S.chartDomain i) (T.chartDomain j)
    (by
      intro x hx
      change localizedSpaceFunctor.map e.hom x ∈ range (T.presentation.atlas.chart j)
      rw [h]
      exact ⟨x, hx, rfl⟩)
    (by
      intro y hy
      change y ∈ range (T.presentation.atlas.chart j) at hy
      rw [h] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      let hₑ := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
      change hₑ.symm (hₑ x) ∈ (S.chartDomain i).carrier
      rw [hₑ.symm_apply_apply]
      exact hx)

private theorem chartDomainIsoOfImage_hom_inclusion
    {S T : SaturatedAtlasPresentation.{u, v, v} K}
    (e : localizationFunctor.obj S ≅ localizationFunctor.obj T)
    (i : S.presentation.atlas.Index) (j : T.presentation.atlas.Index)
    (h : range (T.presentation.atlas.chart j) =
      localizedSpaceFunctor.map e.hom '' range (S.presentation.atlas.chart i)) :
    (chartDomainIsoOfImage e i j h).hom ≫ T.localizedDomainInclusion (T.chartDomain j) =
      S.localizedDomainInclusion (S.chartDomain i) ≫ e.hom :=
  domainRestrictIso_hom_inclusion e _ _ _ _

/-- An analytic-domain embedding can be refined at each source point by a
finite chart neighbourhood whose restrictions are affinoid-domain embeddings. -/
theorem IsAnalyticDomainEmbedding.exists_local_affinoidDomainEmbeddings
    {S W : SaturatedAtlasPresentation.{u, v, v} K}
    {j : localizationFunctor.obj S ⟶ localizationFunctor.obj W}
    (hj : IsAnalyticDomainEmbedding j) (y : S.presentation.space) :
    ∃ I : Set S.presentation.atlas.Index, I.Finite ∧
      (⋃ i ∈ I, range (S.presentation.atlas.chart i)) ∈ 𝓝 y ∧
      ∀ i ∈ I, IsAffinoidDomainEmbedding (S.localizedDomainInclusion (S.chartDomain i) ≫ j) := by
  classical
  obtain ⟨D, e, rfl⟩ := hj
  change W.AnalyticDomain at D
  change localizationFunctor.obj S ≅ localizationFunctor.obj (W.domain D) at e
  let φ := quasiIsoFractionOfIso e
  let T := φ.val.X'
  let eS := localizedQuasiIso φ.val.s φ.val.hs
  let eD := localizedQuasiIso φ.val.f φ.property
  have hw : eS.hom ≫ e.hom = eD.hom := by
    rw [← localizedRightFraction_quasiIsoFractionOfIso e]
    exact localizationFunctor_map_s_comp_localizedRightFraction φ.val
  let h := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eS)
  obtain ⟨σ, hσ, hcharts, _, hn⟩ := T.presentation.atlas.isNet_chartFamily.1 (h.symm y)
  have hgood : ∀ V ∈ σ, ∃ i : S.presentation.atlas.Index,
      range (S.presentation.atlas.chart i) = h '' V ∧
      IsAffinoidDomainEmbedding (S.localizedDomainInclusion (S.chartDomain i) ≫
        (e.hom ≫ domainι (localizationFunctor.obj W) D)) := by
    intro V hV
    obtain ⟨k, rfl⟩ := hcharts hV
    obtain ⟨i, _, hi, _⟩ := exists_chart_image_of_isQuasiIso φ.val.hs k
    obtain ⟨l, _, hl, _⟩ := exists_chart_image_of_isQuasiIso φ.property k
    have hi' : range (S.presentation.atlas.chart i) =
        localizedSpaceFunctor.map eS.hom '' range (T.presentation.atlas.chart k) := by
      change _ = localizedSpaceFunctor.map (localizationFunctor.map φ.val.s) '' _
      rw [localizedSpaceFunctor_map]
      exact hi
    have hl' : range ((W.domain D).presentation.atlas.chart l) =
        localizedSpaceFunctor.map eD.hom '' range (T.presentation.atlas.chart k) := by
      change _ = localizedSpaceFunctor.map (localizationFunctor.map φ.val.f) '' _
      rw [localizedSpaceFunctor_map]
      exact hl
    let dS := chartDomainIsoOfImage eS k i hi'
    let dD := chartDomainIsoOfImage eD k l hl'
    have ha := chartDomainIsoOfImage_hom_inclusion eS k i hi'
    have hb := chartDomainIsoOfImage_hom_inclusion eD k l hl'
    have he : (dS.symm ≪≫ dD).hom ≫
        (W.domain D).localizedDomainInclusion ((W.domain D).chartDomain l) =
        S.localizedDomainInclusion (S.chartDomain i) ≫ e.hom := by
      apply (cancel_epi dS.hom).1
      change dS.hom ≫ (dS.inv ≫ dD.hom) ≫ _ = _
      rw [Category.assoc dS.inv, Iso.hom_inv_id_assoc, hb,
        ← Category.assoc dS.hom, ha, Category.assoc, hw]
    refine ⟨i, hi', ?_⟩
    have hcomp := (isAffinoidDomainEmbedding_domainInclusion_comp W D l).iso_comp
      (dS.symm ≪≫ dD)
    rw [← Category.assoc, he, Category.assoc] at hcomp
    exact hcomp
  choose i hi hfactor using hgood
  refine ⟨{j | ∃ V, ∃ hV : V ∈ σ, i V hV = j}, hσ.dependent_image i, ?_, ?_⟩
  · have hn' : h '' ⋃₀ σ ∈ 𝓝 y := by
      have hn'' : h '' ⋃₀ σ ∈ 𝓝 (h (h.symm y)) := h.isOpenMap.image_mem_nhds hn
      exact (h.apply_symm_apply y) ▸ hn''
    apply Filter.mem_of_superset hn'
    rintro _ ⟨x, ⟨V, hV, hx⟩, rfl⟩
    exact mem_iUnion₂.mpr ⟨i V hV, ⟨V, hV, rfl⟩, (hi V hV).symm ▸ ⟨x, hx, rfl⟩⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact hfactor V hV

/-- At each source point there is a finite neighbourhood of actual domains
through the point, each with a domain–étale factorization over the target. -/
def HasLocalDomainEtaleFactorizations
    {U X : LocalizedCategory.{u, v, v} (K := K)} (f : U ⟶ X) : Prop :=
  ∀ y : localizedSpaceFunctor.obj U,
    ∃ C : Set (presentationOf U).AnalyticDomain, C.Finite ∧
      (⋃ D ∈ C, D.carrier) ∈ 𝓝 y ∧
      ∀ D ∈ C, y ∈ D.carrier ∧ HasDomainEtaleFactorization (domainι U D ≫ f)

/-- Transport the local domains through the source isomorphism, and compose
their étale envelopes with the inverse of the target isomorphism. -/
theorem HasLocalDomainEtaleFactorizations.of_iso
    {U V X Y : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X} {g : V ⟶ Y}
    (h : HasLocalDomainEtaleFactorizations f) (e : V ≅ U) (d : Y ≅ X)
    (w : e.hom ≫ f = g ≫ d.hom) : HasLocalDomainEtaleFactorizations g := by
  intro y
  obtain ⟨C, hC, hn, hg⟩ := h (localizedSpaceFunctor.map e.hom y)
  let E := domainPreimage e.hom '' C
  refine ⟨E, hC.image _, ?_, ?_⟩
  · refine Filter.mem_of_superset
      ((localizedSpaceFunctor.map e.hom).hom.continuous.continuousAt.preimage_mem_nhds hn) ?_
    intro x hx
    obtain ⟨D, hD, hDx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨domainPreimage e.hom D, ⟨D, hD, rfl⟩, hDx⟩
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨hyD, hfD⟩ := hg D hD
    refine ⟨hyD, ?_⟩
    have hfD' := (hfD.iso_comp (domainPreimageIso e D)).comp_iso d.symm
    rw [← Category.assoc (domainPreimageIso e D).hom, domainPreimageIso_hom_inclusion] at hfD'
    let a := domainι V (domainPreimage e.hom D)
    change HasDomainEtaleFactorization (((a ≫ e.hom) ≫ f) ≫ d.inv) at hfD'
    have hw : ((a ≫ e.hom) ≫ f) ≫ d.inv = a ≫ g := by
      rw [Category.assoc a e.hom f, Category.assoc a (e.hom ≫ f), w, Category.assoc g d.hom,
        Iso.hom_inv_id, Category.comp_id]
    exact hw ▸ hfD'

private theorem chartDomain_in_domain {S : SaturatedAtlasPresentation.{u, v, v} K}
    (D : S.AnalyticDomain) (i : (S.domain D).presentation.atlas.Index) :
    ∃ e : localizationFunctor.obj ((S.domain D).domain ((S.domain D).chartDomain i)) ≅
      localizationFunctor.obj (S.domain (S.chartDomain i.val)),
      e.hom ≫ S.localizedDomainInclusion (S.chartDomain i.val) =
        (S.domain D).localizedDomainInclusion ((S.domain D).chartDomain i) ≫
          S.localizedDomainInclusion D := by
  let U := (S.domain D).chartDomain i
  have h : D.subspaceExtend U = S.chartDomain i.val := by
    apply SetLike.coe_injective
    change Subtype.val '' range ((S.domain D).presentation.atlas.chart i) =
      range (S.presentation.atlas.chart i.val)
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(S.domain D).presentation.atlas.chart i z, ⟨z, rfl⟩, rfl⟩
  let e := domainNestedLocalizationIso S D U
  let d := eqToIso (congrArg (fun E => localizationFunctor.obj (S.domain E)) h)
  refine ⟨e ≪≫ d, ?_⟩
  change (e.hom ≫ d.hom) ≫ S.localizedDomainInclusion (S.chartDomain i.val) = _
  rw [Category.assoc, eqToIso_hom_domainInclusion S h, domainNestedLocalizationIso_hom_inclusion]

private theorem isQuasiEtale_of_localDomainEtaleFactorizations
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (f : ofSaturation A ⟶ ofSaturation B)
    (h : HasLocalDomainEtaleFactorizations (localizationFunctor.map f)) : IsQuasiEtale f := by
  classical
  intro y
  let S := ofSaturation A
  obtain ⟨C, hC, hn, hf⟩ := h y
  change Set S.AnalyticDomain at C
  let factorable : S.presentation.atlas.Index → Prop := fun i =>
    ∃ (W : LocalizedCategory.{u, v, v} (K := K))
      (w : W ⟶ localizationFunctor.obj (ofSaturation B))
      (j : localizationFunctor.obj (S.domain (S.chartDomain i)) ⟶ W),
      etale w ∧ IsAffinoidDomainEmbedding j ∧
        j ≫ w = S.localizedDomainInclusion (S.chartDomain i) ≫ localizationFunctor.map f
  have hlocal : ∀ D ∈ C, ∃ I : Set S.presentation.atlas.Index, I.Finite ∧
      (∀ i ∈ I, factorable i) ∧
      ∃ O ∈ 𝓝 y, O ∩ D.carrier ⊆ ⋃ i ∈ I, range (S.presentation.atlas.chart i) := by
    intro D hD
    obtain ⟨hyD, W, j, w, hj, hw, he⟩ := hf D hD
    obtain ⟨W₀, hW₀⟩ := localizedObjectEquiv.surjective W
    change localizationFunctor.obj W₀ = W at hW₀
    subst W
    change localizationFunctor.obj (S.domain D) ⟶ localizationFunctor.obj W₀ at j
    change j ≫ w = S.localizedDomainInclusion D ≫ localizationFunctor.map f at he
    let yD : D.carrier := ⟨y, hyD⟩
    obtain ⟨J, hJ, hJn, hJf⟩ :=
      IsAnalyticDomainEmbedding.exists_local_affinoidDomainEmbeddings
        (S := S.domain D) (W := W₀) hj yD
    obtain ⟨O, hO, hsub⟩ := (mem_nhds_subtype D.carrier yD _).mp hJn
    refine ⟨Subtype.val '' J, hJ.image _, ?_, O, hO, ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      change (S.domain D).presentation.atlas.Index at i
      obtain ⟨e, hinc⟩ := chartDomain_in_domain D i
      let ji := (S.domain D).localizedDomainInclusion ((S.domain D).chartDomain i)
      change e.hom ≫ S.localizedDomainInclusion (S.chartDomain i.val) =
        ji ≫ S.localizedDomainInclusion D at hinc
      refine ⟨_, w, e.inv ≫ (ji ≫ j), hw, (hJf i hi).iso_comp e.symm, ?_⟩
      apply (cancel_epi e.hom).1
      calc
        _ = ji ≫ (j ≫ w) := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
        _ = e.hom ≫ S.localizedDomainInclusion (S.chartDomain i.val) ≫
            localizationFunctor.map f := by
          rw [he, ← Category.assoc ji, ← hinc, Category.assoc]
    · rintro x ⟨hxO, hxD⟩
      obtain ⟨i, hiJ, z, hz⟩ := mem_iUnion₂.mp (hsub (a := ⟨x, hxD⟩) hxO)
      exact mem_iUnion₂.mpr ⟨i.val, ⟨i, hiJ, rfl⟩, ⟨z, congrArg Subtype.val hz⟩⟩
  choose I hI hIf O hO hOi using hlocal
  let I' : Set S.presentation.atlas.Index := ⋃ D : C, I D.val D.property
  let : Finite C := hC.to_subtype
  let chartRange : S.presentation.atlas.Index → Set A.space :=
    fun i => range (S.presentation.atlas.chart i)
  refine ⟨chartRange '' I', (Set.finite_iUnion fun D : C => hI D.val D.property).image _, ?_, ?_⟩
  · have hOn : (⋂ D : C, O D.val D.property) ∈ 𝓝 y :=
      Filter.iInter_mem.mpr fun D => hO D.val D.property
    refine Filter.mem_of_superset (Filter.inter_mem hn hOn) ?_
    rintro x ⟨hx, hOx⟩
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hx
    have hxO := mem_iInter.mp hOx (⟨D, hD⟩ : C)
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hOi D hD ⟨hxO, hxD⟩)
    exact mem_sUnion.mpr ⟨chartRange i, ⟨i, mem_iUnion.mpr ⟨⟨D, hD⟩, hi⟩, rfl⟩, hxi⟩
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨D, hi⟩ := mem_iUnion.mp hi
    exact ⟨i, rfl, hIf D.val D.property i hi⟩

/-- Finite neighbourhoods of analytic domains with explicit domain–étale
factorizations give the original quasi-étale predicate in the localization. -/
theorem HasLocalDomainEtaleFactorizations.quasiEtale
    {U X : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}
    (h : HasLocalDomainEtaleFactorizations f) : quasiEtale f := by
  obtain ⟨S, hS⟩ := localizedObjectEquiv.surjective U
  obtain ⟨B, hB⟩ := localizedObjectEquiv.surjective X
  change localizationFunctor.obj S = U at hS
  change localizationFunctor.obj B = X at hB
  subst U
  subst X
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  let T := φ.X'
  let e := localizationFunctor.mapIso T.saturationIso ≪≫ localizedQuasiIso φ.s φ.hs
  let d := localizationFunctor.mapIso B.saturationIso
  let g : ofSaturation T.presentation ⟶ ofSaturation B.presentation :=
    T.saturationIso.hom ≫ φ.f ≫ B.saturationIso.inv
  have hw : e.hom ≫ localizedRightFraction φ = localizationFunctor.map g ≫ d.hom := by
    change (localizationFunctor.map T.saturationIso.hom ≫ localizationFunctor.map φ.s) ≫
      localizedRightFraction φ = localizationFunctor.map g ≫
        localizationFunctor.map B.saturationIso.hom
    rw [Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction]
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg localizationFunctor.map
    simp only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨T.presentation, B.presentation, g,
    isQuasiEtale_of_localDomainEtaleFactorizations g (h.of_iso e d hw),
    ⟨Arrow.isoMk e d hw⟩⟩

/-- For a Hausdorff source, the given quasi-étale chart neighbourhood can
be taken through the specified point and gives actual domain factorizations. -/
theorem hasLocalDomainEtaleFactorizations_of_quasiEtale
    {U X : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ X} [T2Space (localizedSpaceFunctor.obj U)]
    (h : quasiEtale f) : HasLocalDomainEtaleFactorizations f := by
  classical
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := h
  let eU : localizationFunctor.obj (ofSaturation A) ≅ U := Arrow.leftFunc.mapIso e
  let eX : localizationFunctor.obj (ofSaturation B) ≅ X := Arrow.rightFunc.mapIso e
  have hw : eU.inv ≫ localizationFunctor.map g = f ≫ eX.inv := e.inv.w
  suffices hstrong : HasLocalDomainEtaleFactorizations (localizationFunctor.map g) from
    hstrong.of_iso eU.symm eX.symm hw
  let S := ofSaturation A
  let : T2Space S.presentation.space :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eU)).symm.t2Space
  intro y
  obtain ⟨σ, hσ, hn, hgood⟩ := hg y
  let τ : Set (Set A.space) := {V | V ∈ σ ∧ y ∈ V}
  let δ : Set (Set A.space) := {V | V ∈ σ ∧ y ∉ V}
  have hτ : τ.Finite := hσ.subset fun _ hV => hV.1
  let : Finite δ := (hσ.subset (show δ ⊆ σ from fun _ hV => hV.1)).to_subtype
  have hn' : ⋃₀ τ ∈ 𝓝 y := by
    have hδn : (⋂ V : δ, V.valᶜ) ∈ 𝓝 y := by
      refine Filter.iInter_mem.mpr fun V => ?_
      obtain ⟨i, hi, _⟩ := hgood V.val V.property.1
      have hc : IsCompact (range (S.presentation.atlas.chart i)) :=
        isCompact_range (S.presentation.atlas.isEmbedding_chart i).continuous
      have hclosed : IsClosed V.val := hi ▸ hc.isClosed
      exact hclosed.isOpen_compl.mem_nhds V.property.2
    refine Filter.mem_of_superset (Filter.inter_mem hn hδn) ?_
    rintro x ⟨⟨V, hV, hx⟩, hδx⟩
    by_cases hy : y ∈ V
    · exact mem_sUnion.mpr ⟨V, ⟨hV, hy⟩, hx⟩
    · exact False.elim ((mem_iInter.mp hδx (⟨V, hV, hy⟩ : δ)) hx)
  have hchart : ∀ V : τ, ∃ i : S.presentation.atlas.Index,
      range (S.presentation.atlas.chart i) = V.val ∧
      HasDomainEtaleFactorization
        (S.localizedDomainInclusion (S.chartDomain i) ≫ localizationFunctor.map g) := by
    intro V
    obtain ⟨i, hi, W, w, j, hw, hj, he⟩ := hgood V.val V.property.1
    exact ⟨i, hi, W, j, w, hj.isAnalyticDomainEmbedding, hw, he⟩
  choose i hi hfactor using hchart
  let : Finite τ := hτ.to_subtype
  let chart : τ → S.AnalyticDomain := fun V => S.chartDomain (i V)
  refine ⟨range chart, Set.finite_range _, ?_, ?_⟩
  · refine Filter.mem_of_superset hn' ?_
    rintro x ⟨V, hV, hx⟩
    let V' : τ := ⟨V, hV⟩
    have hx' : x ∈ range (S.presentation.atlas.chart (i V')) := (hi V').symm ▸ hx
    exact mem_iUnion₂.mpr ⟨chart V', ⟨V', rfl⟩, hx'⟩
  · rintro _ ⟨V, rfl⟩
    have hy : y ∈ range (S.presentation.atlas.chart (i V)) := (hi V).symm ▸ V.property.2
    exact ⟨hy, hfactor V⟩

end Langlands.Analytic.SaturatedAtlasPresentation
