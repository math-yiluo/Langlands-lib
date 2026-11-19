import Langlands.Geometry.Analytic.DomainEtalePullbacks
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.QuasiEtaleDomainIntersections
import Langlands.Geometry.Analytic.QuasiEtaleDomainLocality
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Domain factorizations in actual localized pullbacks -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section DomainIntersection

variable {A B X P : LocalizedCategory.{u, v, v} (K := K)}
  {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B}
  (h : IsPullback p q f g)
  (D : (presentationOf A).AnalyticDomain) (E : (presentationOf B).AnalyticDomain)

include h in
/-- Restrict both factors of a full analytic pullback by intersecting
the two inverse-image domains in its point. -/
theorem isPullback_domainPreimage_inf :
    IsPullback
      (domainOrderMap (inf_le_left : domainPreimage p D ⊓ domainPreimage q E ≤
        domainPreimage p D) ≫ domainPreimageMap p D)
      (domainOrderMap (inf_le_right : domainPreimage p D ⊓ domainPreimage q E ≤
        domainPreimage q E) ≫ domainPreimageMap q E)
      (domainι A D ≫ f) (domainι B E ≫ g) :=
  ((domainIntersection_isPullback (domainPreimage p D) (domainPreimage q E)).paste_horiz
    (domainPreimage_isPullback p D).flip).paste_vert
      (isPullback_domainPreimage_comp h.flip E).flip

end DomainIntersection

/-- Stability of the actual localized étale predicate under existing
pullbacks, with independent field and common space and index universes. -/
def LocalizedEtaleBaseChangeStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  (etale (K := K) :
    MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange

section BaseChange

variable [(etale (K := K) :
    MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange]
  {A B X P : LocalizedCategory.{u, v, v} (K := K)}
  {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B}

/-- An explicit domain–étale factorization pulls back by restricting the
pullback of the étale envelope to the inverse-image domain. -/
theorem HasDomainEtaleFactorization.of_isPullback
    (hf : HasDomainEtaleFactorization f) (h : IsPullback p q f g) :
    HasDomainEtaleFactorization q := by
  obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, rfl⟩ := hf
  let c := localizedEtalePullback w g hw
  have hc : IsPullback c.1.fst c.1.snd w g := IsPullback.of_isLimit c.2
  have he : etale c.1.snd := MorphismProperty.IsStableUnderBaseChange.of_isPullback hc hw
  let F := domainPreimage c.1.fst D
  have hd := isPullback_domainPreimage_comp hc D
  have h' : IsPullback (p ≫ e.hom) q (domainι W D ≫ w) g := by
    apply h.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp [Category.assoc]
    · simp
  let i := h'.isoIsPullback _ _ hd
  exact ⟨c.1.pt, i.hom ≫ domainι c.1.pt F, c.1.snd,
    (isAnalyticDomainEmbedding_domainι c.1.pt F).iso_comp i, he,
    (Category.assoc _ _ _).trans (h'.isoIsPullback_hom_snd _ _ hd)⟩

/-- Local domain–étale factorizations pull back to the literal inverse-image
neighbourhoods in the full localized pullback. -/
theorem HasLocalDomainEtaleFactorizations.of_isPullback
    (hf : HasLocalDomainEtaleFactorizations f) (h : IsPullback p q f g) :
    HasLocalDomainEtaleFactorizations q := by
  intro z
  obtain ⟨C, hC, hn, hfC⟩ := hf (localizedSpaceFunctor.map p z)
  refine ⟨domainPreimage p '' C, hC.image _, ?_, ?_⟩
  · refine Filter.mem_of_superset
      ((localizedSpaceFunctor.map p).hom.continuous.continuousAt.preimage_mem_nhds hn) ?_
    intro x hx
    obtain ⟨D, hD, hDx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨domainPreimage p D, ⟨D, hD, rfl⟩, hDx⟩
  · rintro _ ⟨D, hD, rfl⟩
    exact ⟨(hfC D hD).1, (hfC D hD).2.of_isPullback (isPullback_domainPreimage_comp h D)⟩

/-- Given domain–étale factorizations on both factors, their product over
the common target is a domain of the product of the two étale envelopes. -/
theorem HasDomainEtaleFactorization.of_isPullback_comp
    (hf : HasDomainEtaleFactorization f) (hg : HasDomainEtaleFactorization g)
    (h : IsPullback p q f g) : HasDomainEtaleFactorization (q ≫ g) := by
  obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, rfl⟩ := hf
  obtain ⟨V, _, v, ⟨E, d, rfl⟩, hv, rfl⟩ := hg
  let c := localizedEtalePullback w v hw
  have hc : IsPullback c.1.fst c.1.snd w v := IsPullback.of_isLimit c.2
  have he : etale c.1.snd := MorphismProperty.IsStableUnderBaseChange.of_isPullback hc hw
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
    (isAnalyticDomainEmbedding_domainι c.1.pt F).iso_comp i, etale_comp he hv, ?_⟩
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
theorem HasLocalDomainEtaleFactorizations.of_isPullback_comp
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
    have hfact := (hfC D hD).2.of_isPullback_comp (hgE T hT).2 hd
    simpa only [Category.assoc, domainPreimageMap_comp_inclusion_assoc,
      domainOrderMap_comp_inclusion_assoc] using hfact

end BaseChange

end Langlands.Analytic.SaturatedAtlasPresentation
