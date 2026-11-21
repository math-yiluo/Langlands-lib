import Langlands.Geometry.Analytic.AnalyticOpenImmersionBaseChange
import Langlands.Geometry.Analytic.DomainEtalePullbacks
import Langlands.Geometry.Analytic.EtaleDomainTargetCancellation
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.QuasiEtaleDomainLocality
import Langlands.Geometry.Analytic.QuasiEtaleOpenRestrictionStatement

/-! # Quasi-étale restriction over an open analytic domain -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- In a pullback along an open inclusion, the domain factor pulls back to a domain
in the open restriction of the étale envelope. -/
private theorem factorization_of_openDomain_pullback
    {A Z P : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ Z}
    {V : Set (presentationOf Z).presentation.space} {hV : IsOpen V}
    {p : P ⟶ A} {q : P ⟶ domainObj Z ((presentationOf Z).openDomain V hV)}
    (hf : HasDomainEtaleFactorization f)
    (h : IsPullback p q f (domainι Z ((presentationOf Z).openDomain V hV))) :
    HasDomainEtaleFactorization q := by
  obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, rfl⟩ := hf
  let W' := domainObj W (preimageOpenDomain w V hV)
  let w' := preimageOpenDomainMap w V hV
  have hw' : etale w' := by
    apply etale_of_comp_domainι ((presentationOf Z).openDomain V hV)
    rw [show w' = preimageOpenDomainMap w V hV from rfl, preimageOpenDomainMap_comp]
    exact etale_comp (etaleOpenDomainStatement W _ _) hw
  let E := domainPreimage (domainι W (preimageOpenDomain w V hV)) D
  have hE := isPullback_domainPreimage_comp (isPullback_preimageOpenDomain w V hV).flip D
  have h' : IsPullback (p ≫ e.hom) q (domainι W D ≫ w)
      (domainι Z ((presentationOf Z).openDomain V hV)) := by
    apply h.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp [Category.assoc]
    · simp
  let i := h'.isoIsPullback _ _ hE
  exact ⟨W', i.hom ≫ domainι W' E, w', (isAnalyticDomainEmbedding_domainι W' E).iso_comp i,
    hw', (Category.assoc _ _ _).trans (h'.isoIsPullback_hom_snd _ _ hE)⟩

/-- The actual restriction of a quasi-étale map with Hausdorff source to an
open subset of the target is quasi-étale. -/
theorem quasiEtaleOpenRestriction : QuasiEtaleOpenRestrictionStatement.{u, v} := by
  intro K _ _ _ Y Z _ f hf V hV
  let r := preimageOpenDomainMap f V hV
  let p := domainι Y (preimageOpenDomain f V hV)
  change quasiEtale r
  refine HasLocalDomainEtaleFactorizations.quasiEtale (f := r) ?_
  intro y
  obtain ⟨C, hC, hn, hfact⟩ :=
    hasLocalDomainEtaleFactorizations_of_quasiEtale hf (localizedSpaceFunctor.map p y)
  refine ⟨domainPreimage p '' C, hC.image _, ?_, ?_⟩
  · refine Filter.mem_of_superset
      ((localizedSpaceFunctor.map p).hom.continuous.continuousAt.preimage_mem_nhds hn) ?_
    intro x hx
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨domainPreimage p D, ⟨D, hD, rfl⟩, hxD⟩
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨hyD, hfD⟩ := hfact D hD
    exact ⟨hyD, factorization_of_openDomain_pullback hfD
      (isPullback_domainPreimage_comp (isPullback_preimageOpenDomain f V hV).flip D)⟩

end Langlands.Analytic.SaturatedAtlasPresentation
