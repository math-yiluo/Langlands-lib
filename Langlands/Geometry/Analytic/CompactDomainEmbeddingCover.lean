import Langlands.Geometry.Analytic.QuasiEtaleDomainIntersections
import Langlands.Geometry.Analytic.SaturatedDomainHomPresheaf

/-! # Analytic-domain embeddings from finite compact domain covers -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem range_iso_comp_domainι
    {A B : LocalizedCategory.{u, v, w} (K := K)} (D : (presentationOf B).AnalyticDomain)
    (e : A ≅ domainObj B D) :
    range (localizedSpaceFunctor.map (e.hom ≫ domainι B D)) = D.carrier := by
  have h (x : localizedSpaceFunctor.obj A) :
      localizedSpaceFunctor.map (e.hom ≫ domainι B D) x =
        (localizedSpaceFunctor.map e.hom x).val := by
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact h x ▸ (localizedSpaceFunctor.map e.hom x).property
  · intro hy
    obtain ⟨x, hx⟩ :=
      (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)).surjective ⟨y, hy⟩
    exact ⟨x, (h x).trans (congrArg Subtype.val hx)⟩

private theorem domainCover_hom_ext
    {P : SaturatedAtlasPresentation.{u, v, v} K} {ι : Type z}
    (S : P.AnalyticDomain) (D : ι → P.AnalyticDomain) (hDS : ∀ i, D i ≤ S)
    (hcov : AtlasTopology.LocallyRefines (range (fun i => (D i).carrier)) {S.carrier})
    {f g : localizationFunctor.obj (P.domain S) ⟶ localizationFunctor.obj P}
    (h : ∀ i, domainOrderMap (U := localizationFunctor.obj P) (hDS i) ≫ f =
      domainOrderMap (U := localizationFunctor.obj P) (hDS i) ≫ g) : f = g := by
  let F := SourceCategory.comparisonFunctor (K := K)
  let f₀ : SourceCategory.ofPresentation (P.originalDomain S) ⟶ SourceCategory.ofPresentation P :=
    F.preimage f
  let g₀ : SourceCategory.ofPresentation (P.originalDomain S) ⟶ SourceCategory.ofPresentation P :=
    F.preimage g
  have hf : F.map f₀ = f := F.map_preimage f
  have hg : F.map g₀ = g := F.map_preimage g
  have he : f₀ = g₀ := SourceCategory.eq_of_relativeDomainCover S D hDS hcov f₀ g₀ (by
    intro i
    apply F.map_injective
    have hi : F.map (SourceCategory.domainMap (hDS i)) =
        domainOrderMap (U := localizationFunctor.obj P) (hDS i) := by
      apply (cancel_mono (P.localizedDomainInclusion S)).1
      have hw := congrArg F.map (SourceCategory.domainMap_inclusion (hDS i))
      rw [Functor.map_comp] at hw
      change F.map (SourceCategory.domainMap (hDS i)) ≫
        SourceCategory.comparisonFunctor.map (SourceCategory.domainInclusion P S) =
        SourceCategory.comparisonFunctor.map (SourceCategory.domainInclusion P (D i)) at hw
      rw [P.comparisonFunctor_map_domainInclusion, P.comparisonFunctor_map_domainInclusion] at hw
      exact hw.trans (domainOrderMap_comp_inclusion
        (U := localizationFunctor.obj P) (hDS i)).symm
    rw [Functor.map_comp, Functor.map_comp, hi, hf, hg]
    exact h i)
  exact hf.symm.trans ((congrArg F.map he).trans hg)

variable {A B : LocalizedCategory.{u, v, v} (K := K)}

/-- A finite cover by compact analytic domains on which a map induces
analytic-domain embeddings. -/
structure FiniteCompactDomainEmbeddingCover (f : A ⟶ B) where
  Index : Type v
  finite : Finite Index
  domain : Index → (presentationOf A).AnalyticDomain
  compact : ∀ i, IsCompactSpace (domainObj A (domain i))
  covers : ∀ x : localizedSpaceFunctor.obj A, ∃ i, x ∈ (domain i).carrier
  embedding : ∀ i, IsAnalyticDomainEmbedding (domainι A (domain i) ≫ f)

/-- A split analytic map which is a domain embedding on a finite compact
domain cover identifies its Hausdorff source with a single analytic domain. -/
theorem FiniteCompactDomainEmbeddingCover.isAnalyticDomainEmbedding
    {f : A ⟶ B} (C : FiniteCompactDomainEmbeddingCover f)
    [T2Space (localizedSpaceFunctor.obj A)] (r : B ⟶ A) (hr : f ≫ r = 𝟙 A) :
    IsAnalyticDomainEmbedding f := by
  classical
  obtain ⟨P, hP⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj P = B at hP
  subst B
  let : Finite C.Index := C.finite
  choose D e he using C.embedding
  change C.Index → P.AnalyticDomain at D
  let Y : Set P.presentation.space := range (localizedSpaceFunctor.map f)
  let fsp := localizedSpaceFunctor.map f
  let rsp := localizedSpaceFunctor.map r
  have hleft : Function.LeftInverse rsp fsp := by
    intro x
    have h := congrArg (fun k : A ⟶ A => localizedSpaceFunctor.map k x) hr
    change rsp (fsp x) = x
    rw [Functor.map_comp, localizedSpaceFunctor.map_id A] at h
    exact h
  let : T2Space Y :=
    (hleft.isEmbedding rsp.hom.continuous fsp.hom.continuous).toHomeomorph.t2Space
  have hi (i : C.Index) :
      range (localizedSpaceFunctor.map (domainι A (C.domain i) ≫ f)) = (D i).carrier := by
    rw [he i]
    exact range_iso_comp_domainι (B := localizationFunctor.obj P) (D i) (e i)
  have hDY (i : C.Index) : (D i).carrier ⊆ Y := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hi i).symm ▸ hy
    refine ⟨x.val, ?_⟩
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply]
  have hcov (y : Y) : ∃ i, y.val ∈ (D i).carrier := by
    obtain ⟨x, hx⟩ := y.property
    obtain ⟨i, hiC⟩ := C.covers x
    refine ⟨i, (hi i) ▸ ?_⟩
    let a : localizedSpaceFunctor.obj (domainObj A (C.domain i)) := ⟨x, hiC⟩
    refine ⟨a, ?_⟩
    rw [Functor.map_comp]
    change localizedSpaceFunctor.map f (localizedSpaceFunctor.map (domainι A (C.domain i)) a) = _
    rw [domainι_apply]
    exact hx
  let D' (i : C.Index) : Set Y := Subtype.val ⁻¹' (D i).carrier
  have hfamily : AtlasTopology.restrictedFamily (range (fun i => (D i).carrier)) Y =
      range D' := by
    ext V
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(D i).carrier, ⟨i, rfl⟩, hDY i, rfl⟩
  have hquasi : AtlasTopology.IsQuasinet (range D') := by
    refine AtlasTopology.isQuasinet_of_finite_closedCover (range D') (finite_range _) ?_ ?_ ?_
    · exact Subset.rfl
    · rintro _ ⟨i, rfl⟩
      let : CompactSpace (localizedSpaceFunctor.obj (domainObj A (C.domain i))) :=
        (C.compact i).1
      have hDc : IsCompact (D i).carrier := isCompact_iff_compactSpace.mpr
        (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (e i))).compactSpace
      have h : IsCompact (D' i) := Topology.IsInducing.subtypeVal.isCompact_preimage' hDc
        (by simpa only [Subtype.range_coe] using hDY i)
      exact h.isClosed
    · apply eq_univ_of_forall
      intro y
      obtain ⟨i, hi⟩ := hcov y
      exact mem_sUnion.mpr ⟨D' i, ⟨i, rfl⟩, hi⟩
  have hDref : AtlasTopology.LocallyRefines (range (fun i => (D i).carrier)) {Y} :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp (hfamily.symm ▸ hquasi)
  have hChartRef : AtlasTopology.LocallyRefines (range (fun i => range (P.presentation.atlas.chart i)))
      (range (fun i => (D i).carrier)) := by
    rintro _ ⟨i, rfl⟩
    exact (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp (D i).is_domain _
      (mem_singleton _)
  let E : P.AnalyticDomain :=
    ⟨Y, (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr (hDref.trans hChartRef)⟩
  have hDE (i : C.Index) : D i ≤ E := hDY i
  let m := domainLift (X := localizationFunctor.obj P) E f (fun x => mem_range_self x)
  let j := domainι (localizationFunctor.obj P) E
  have hm : m ≫ j = f := domainLift_comp (X := localizationFunctor.obj P) E f _
  have hmr : m ≫ (j ≫ r) = 𝟙 A := by
    rw [← Category.assoc, hm, hr]
  have hproj : (j ≫ r) ≫ f = j := by
    apply domainCover_hom_ext E D hDE hDref
    intro i
    let l := (e i).inv ≫ domainι A (C.domain i)
    have hl : l ≫ f = domainι (localizationFunctor.obj P) (D i) := by
      change ((e i).inv ≫ domainι A (C.domain i)) ≫ f = _
      rw [Category.assoc, he i, Iso.inv_hom_id_assoc]
    let k := domainOrderMap (U := localizationFunctor.obj P) (hDE i)
    have hk : k ≫ j = domainι (localizationFunctor.obj P) (D i) :=
      domainOrderMap_comp_inclusion (U := localizationFunctor.obj P) (hDE i)
    calc
      _ = (k ≫ j) ≫ (r ≫ f) := by
        change k ≫ ((j ≫ r) ≫ f) = _
        simp only [Category.assoc]
      _ = domainι (localizationFunctor.obj P) (D i) ≫ (r ≫ f) := by rw [hk]
      _ = domainι (localizationFunctor.obj P) (D i) := by
        rw [← hl, Category.assoc, ← Category.assoc f, hr, Category.id_comp]
      _ = _ := hk.symm
  have hrm : (j ≫ r) ≫ m = 𝟙 _ := by
    let : Mono j := domainι_mono (X := localizationFunctor.obj P) E
    apply (cancel_mono j).1
    rw [Category.assoc, hm, hproj, Category.id_comp]
  exact ⟨E, ⟨m, j ≫ r, hmr, hrm⟩, hm.symm⟩

end Langlands.Analytic.SaturatedAtlasPresentation
