import Langlands.Geometry.Analytic.EtaleOpenDomains.Statement
import Langlands.Geometry.Analytic.QuasiEtaleDomains
import Langlands.Geometry.Analytic.PairSystemLocalizedMorphisms

/-! # Transport of étaleness of open-domain inclusions -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- The canonical domain inclusions are isomorphic as arrows under a domain-preserving
isomorphism of ambient spaces. -/
def domainInclusionArrowIso (e : X ≅ Y) (D : (presentationOf X).AnalyticDomain)
    (E : (presentationOf Y).AnalyticDomain)
    (hf : ∀ x ∈ D.carrier, localizedSpaceFunctor.map e.hom x ∈ E.carrier)
    (hg : ∀ y ∈ E.carrier, localizedSpaceFunctor.map e.inv y ∈ D.carrier) :
    Arrow.mk (domainι X D) ≅ Arrow.mk (domainι Y E) :=
  Arrow.isoMk (domainRestrictIso e D E hf hg) e (domainRestrict_comp D E e.hom hf)

/-- Étaleness of all open-domain inclusions transports along an isomorphism of analytic
spaces. -/
theorem etaleOpenDomainStatement_of_iso (e : X ≅ Y) (hY : EtaleOpenDomainStatement Y) :
    EtaleOpenDomainStatement X := by
  intro U hU
  let V : Set (localizedSpaceFunctor.obj Y) := localizedSpaceFunctor.map e.inv ⁻¹' U
  have hV : IsOpen V := hU.preimage (localizedSpaceFunctor.map e.inv).hom.continuous
  have hfg (x : localizedSpaceFunctor.obj X) :
      localizedSpaceFunctor.map e.inv (localizedSpaceFunctor.map e.hom x) = x := by
    rw [← TopCat.comp_app, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id]
    rfl
  have hf : ∀ x ∈ U, localizedSpaceFunctor.map e.hom x ∈ V := by
    intro x hx
    change localizedSpaceFunctor.map e.inv (localizedSpaceFunctor.map e.hom x) ∈ U
    rw [hfg]
    exact hx
  exact ((etale (K := K)).arrow_mk_iso_iff
    (domainInclusionArrowIso e ((presentationOf X).openDomain U hU)
      ((presentationOf Y).openDomain V hV) hf (fun _ hy => hy))).2 (hY V hV)

/-- It suffices to prove étaleness of open-domain inclusions on the full-recognition
presentations: every analytic space is isomorphic to one of these. -/
theorem etaleOpenDomainStatement_of_fullRecognition
    (hfull : ∀ (P : AffinoidAtlasPresentation.{u, v, v} K) (U : Set P.space) (hU : IsOpen U),
      etale ((ofFullRecognition P).localizedDomainInclusion
        ((ofFullRecognition P).openDomain U hU)))
    (X : LocalizedCategory.{u, v, v} (K := K)) : EtaleOpenDomainStatement X := by
  let S := presentationOf X
  let e : X ≅ localizationFunctor.obj (ofFullRecognition S.presentation) :=
    (localizationFunctor.mapIso S.saturationIso).symm ≪≫
      localizedQuasiIso
        (AffinoidAtlasPresentation.StrongHom.localDomainToFullRecognitionHom S.presentation)
        S.presentation.localDomainToFullRecognition_isQuasiIso
  apply etaleOpenDomainStatement_of_iso e
  exact hfull S.presentation

end Langlands.Analytic.SaturatedAtlasPresentation
