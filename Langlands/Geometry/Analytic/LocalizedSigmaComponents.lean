import Langlands.Geometry.Analytic.DisjointUnionDomainEmbeddings
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.SaturatedDomainCorestriction

/-! # Étaleness of the inclusions of the pieces of a disjoint union -/

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace SaturatedAtlasPresentation

section DomainEmbeddings

variable {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- A domain embedding whose image is an analytic domain `S` factors, after a refinement of
its source atlas, through a quasi-isomorphism onto the domain `S`. -/
theorem isQuasiIso_domainFactor (f : A ⟶ B) (hf : f.IsDomainEmbedding)
    (S : B.presentation.atlas.OriginalChartDomain) (himage : ∀ x, f.baseMap x ∈ S)
    (hsurj : ∀ y ∈ S.carrier, ∃ x, f.baseMap x = y) :
    (domainFactor f S himage).IsQuasiIso := by
  refine ⟨?_, ?_⟩
  · rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨hf.1.codRestrict _ himage, ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y hy
    exact ⟨x, rfl⟩
  · intro i j h
    have hl : (domainFactor f S himage).chartImageLocus i j =
        f.chartImageLocus i.val j.val := by
      ext y
      constructor
      · rintro ⟨x, ⟨z, rfl⟩, hx⟩
        exact ⟨_, ⟨z, rfl⟩, congrArg Subtype.val hx⟩
      · rintro ⟨x, ⟨z, rfl⟩, hx⟩
        exact ⟨_, ⟨z, rfl⟩, Subtype.ext hx⟩
    rw [hl]
    exact hf.2 i.val j.val ((domainBaseMap_admissible_iff f S himage i.val j).mp h)

end DomainEmbeddings

/-- The image in the localized category of a domain embedding with open image is étale. -/
theorem etale_localizationFunctor_map_of_isDomainEmbedding
    {A B : SaturatedAtlasPresentation.{u, v, v} K} (f : A ⟶ B) (hf : f.IsDomainEmbedding)
    (hU : IsOpen (Set.range f.baseMap)) : etale (localizationFunctor.map f) := by
  let D := B.openDomain _ hU
  have himage : ∀ x, f.baseMap x ∈ D := fun x => ⟨x, rfl⟩
  let P := domainSourceSelection f D himage
  have hq := isQuasiIso_domainFactor f hf D himage (fun _ hy => hy)
  have hr := isQuasiIso_refiningSubatlasInclusion P
  have key : localizationFunctor.map f =
      (localizedQuasiIso _ hr).inv ≫ localizationFunctor.map (domainFactor f D himage) ≫
        localizationFunctor.map (B.originalDomainInclusion D) := by
    rw [← Functor.map_comp, domainFactor_comp_inclusion f D himage, Functor.map_comp,
      ← localizedQuasiIso_hom _ hr, Iso.inv_hom_id_assoc]
  rw [key]
  refine etale_comp (etale_of_isIso _) (etale_comp ?_ ?_)
  · exact etale_of_isIso (localizedQuasiIso _ hq).hom
  · exact etaleOpenDomainStatement (localizationFunctor.obj B) _ hU

variable {J : Type z}

/-- The inclusions of the pieces of a disjoint union of analytic spaces are étale. -/
theorem etale_localizedSigmaCofan_inj
    (X : J → LocalizedCategory.{u, max z v, max z v} (K := K)) (j : J) :
    etale ((localizedSigmaCofan X).inj j) := by
  let T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K :=
    fun j => localizedObjectEquiv.symm (X j)
  change etale ((Localization.isoOfHom localizationFunctor quasiIsomorphisms _
      (isQuasiIso_nonemptyReplacementHom (T j))).inv ≫
    localizationFunctor.map ((sigmaCofan T).inj j))
  refine etale_comp (etale_of_isIso _) ?_
  refine etale_localizationFunctor_map_of_isDomainEmbedding _
    (isDomainEmbedding_sigmaCofan_inj T j) ?_
  exact isOpen_range_sigmaMk (σ := fun j => (nonemptyFamily T j).space)

end SaturatedAtlasPresentation

end Langlands.Analytic
