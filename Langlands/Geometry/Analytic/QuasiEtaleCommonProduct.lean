import Langlands.Geometry.Analytic.QuasiEtalePullbackLocality
import Langlands.Geometry.Analytic.LocalizedCommonEtaleProduct

/-! # Common structure maps of quasi-étale products -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set Filter Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B X P : LocalizedCategory.{u, v, v} (K := K)}
  {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B}

/-- Given domain–étale factorizations on both factors, their product over
the common target is a domain of the product of the two étale envelopes. -/
theorem HasDomainEtaleFactorization.of_isPullback_common
    (hf : HasDomainEtaleFactorization f) (hg : HasDomainEtaleFactorization g)
    (h : IsPullback p q f g) : HasDomainEtaleFactorization (q ≫ g) := by
  obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, rfl⟩ := hf
  obtain ⟨V, _, v, ⟨E, d, rfl⟩, hv, rfl⟩ := hg
  let c := localizedEtalePullback w v hw
  have hc : IsPullback c.1.fst c.1.snd w v := IsPullback.of_isLimit c.2
  have he : etale (c.1.snd ≫ v) := hc.w ▸ etale_common_of_isPullback hc hw hv
  let F := domainPreimage c.1.fst D ⊓ domainPreimage c.1.snd E
  have hd := isPullback_domainPreimage_inf hc D E
  have h' : IsPullback (p ≫ e.hom) (q ≫ d.hom) (domainι W D ≫ w) (domainι V E ≫ v) := by
    apply h.of_iso (Iso.refl _) e d (Iso.refl _)
    · simp
    · simp
    · simp [Category.assoc]
    · simp [Category.assoc]
  let i := h'.isoIsPullback _ _ hd
  refine ⟨c.1.pt, i.hom ≫ domainι c.1.pt F, c.1.snd ≫ v,
    (isAnalyticDomainEmbedding_domainι c.1.pt F).iso_comp i, he, ?_⟩
  let s := domainOrderMap (inf_le_right : F ≤ domainPreimage c.1.snd E) ≫
    domainPreimageMap c.1.snd E
  have hF : domainι c.1.pt F ≫ c.1.snd = s ≫ domainι V E := by
    simp only [s, Category.assoc, domainPreimageMap_comp_inclusion,
      domainOrderMap_comp_inclusion_assoc]
    rfl
  have hs : i.hom ≫ s = q ≫ d.hom := h'.isoIsPullback_hom_snd _ _ hd
  calc
    _ = i.hom ≫ (domainι c.1.pt F ≫ c.1.snd) ≫ v := by simp only [Category.assoc]
    _ = (i.hom ≫ s) ≫ (domainι V E ≫ v) := by
      rw [hF]
      simp only [Category.assoc]
    _ = _ := by
      rw [hs]
      simp only [Category.assoc]

/-- Paired finite domain neighbourhoods produce a finite domain
neighbourhood of each point of a pullback of two locally factorizable maps. -/
theorem HasLocalDomainEtaleFactorizations.of_isPullback_common
    (hf : HasLocalDomainEtaleFactorizations f) (hg : HasLocalDomainEtaleFactorizations g)
    (h : IsPullback p q f g) : HasLocalDomainEtaleFactorizations (q ≫ g) := by
  intro z
  obtain ⟨C, hC, hn, hfC⟩ := hf (localizedSpaceFunctor.map p z)
  obtain ⟨E, hE, hm, hgE⟩ := hg (localizedSpaceFunctor.map q z)
  let F : (presentationOf A).AnalyticDomain × (presentationOf B).AnalyticDomain →
      (presentationOf P).AnalyticDomain :=
    fun de => domainPreimage p de.1 ⊓ domainPreimage q de.2
  refine ⟨F '' (C ×ˢ E), (hC.prod hE).image _, ?_, ?_⟩
  · have hp := (localizedSpaceFunctor.map p).hom.continuous.continuousAt.preimage_mem_nhds hn
    have hq := (localizedSpaceFunctor.map q).hom.continuous.continuousAt.preimage_mem_nhds hm
    refine Filter.mem_of_superset (Filter.inter_mem hp hq) ?_
    rintro x ⟨hx, hy⟩
    obtain ⟨D, hD, hDx⟩ := mem_iUnion₂.mp hx
    obtain ⟨T, hT, hTx⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨F (D, T), ⟨(D, T), ⟨hD, hT⟩, rfl⟩, ⟨hDx, hTx⟩⟩
  · rintro _ ⟨⟨D, T⟩, ⟨hD, hT⟩, rfl⟩
    refine ⟨⟨(hfC D hD).1, (hgE T hT).1⟩, ?_⟩
    have hd := isPullback_domainPreimage_inf h D T
    have hfact := (hfC D hD).2.of_isPullback_common (hgE T hT).2 hd
    simpa only [Category.assoc, domainPreimageMap_comp_inclusion_assoc,
      domainOrderMap_comp_inclusion_assoc] using hfact

set_option linter.defProp false in
/-- The common map of a product of two Hausdorff quasi-étale factors
is quasi-étale over their original base. -/
def quasiEtale_common_of_isPullback
    [T2Space (localizedSpaceFunctor.obj A)] [T2Space (localizedSpaceFunctor.obj B)]
    (h : IsPullback p q f g) (hf : quasiEtale f) (hg : quasiEtale g) : quasiEtale (q ≫ g) :=
  ((hasLocalDomainEtaleFactorizations_of_quasiEtale hf).of_isPullback_common
    (hasLocalDomainEtaleFactorizations_of_quasiEtale hg) h).quasiEtale

end Langlands.Analytic.SaturatedAtlasPresentation
