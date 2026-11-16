import Langlands.Geometry.Analytic.EtaleSite
import Langlands.Geometry.Analytic.AdmissibleEpimorphism
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Open and closed immersions of analytic spaces -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

namespace BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w}
  [NormedField K] [NormedCommRing R] [NormedCommRing S]
  [NormedAlgebra K R] [NormedAlgebra K S]

/-- An admissible epimorphism is a finite Banach algebra map, with the single
generator `1`. -/
theorem IsAdmissibleEpi.isFiniteBanach {f : BoundedAlgHom K R S} (hf : f.IsAdmissibleEpi) :
    f.IsFiniteBanach := by
  obtain ⟨C, hC, hlifts⟩ := f.isAdmissibleEpi_iff_normControlledLifts.mp hf
  refine ⟨1, fun _ => 1, C, hC, fun y => ?_⟩
  obtain ⟨a, ha, hna⟩ := hlifts y
  refine ⟨fun _ => a, ?_, ?_⟩
  · rw [coefficientMap_apply, Fin.sum_univ_one, mul_one, ha]
  · exact (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (norm_nonneg y))).2 fun _ => hna

end BoundedAlgHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Berkovich's closed immersions, in the form of Lemma 1.3.7(b) of the étale
cohomology paper: the preimage of every affinoid domain `W` of the target is an
affinoid domain of the source, and the bounded map from the affinoid algebra of `W`
to that of its preimage is an admissible epimorphism, which is a closed immersion
of affinoid spaces. -/
def IsClosedImmersion (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    Prop :=
  ∀ W : B.atlas.saturatedAtlas.RecognizedSubset,
    ∃ (V : A.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart),
      V.locus = g.baseMap ⁻¹' W.locus ∧
        (g.fullRecognitionPairs.pullback V W h).IsAdmissibleEpi

variable {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- Closed immersions are finite morphisms. -/
theorem IsClosedImmersion.isFinite (hg : g.IsClosedImmersion) : g.IsFinite := by
  refine ⟨Set.subset_univ _, fun W _ => ?_⟩
  obtain ⟨V, h, hV, hadm⟩ := hg W
  exact ⟨V, h, hV.trans (Set.univ_inter _).symm, hadm.isFiniteBanach⟩

variable (A)

/-- The identity strong map is a closed immersion. -/
theorem isClosedImmersion_id : (StrongHom.id A.saturatedPresentation).IsClosedImmersion := by
  intro W
  have h : (StrongHom.id A.saturatedPresentation).baseMap '' Set.range W.chart ⊆
      Set.range W.chart := fun _ ⟨x, hx, e⟩ => e ▸ hx
  refine ⟨W, h, rfl, ?_⟩
  rw [fullRecognitionPairs_id_pullback_self A W h]
  exact BoundedAlgHom.isAdmissibleEpi_id

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

/-- Closed immersions in the localized category of analytic spaces: arrows
isomorphic, in the arrow category, to the image of a closed immersion between
constructed saturations. -/
def closedImmersion : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)) :=
  fun _ _ φ =>
    ∃ (A B : AffinoidAtlasPresentation.{u, v, v} K) (g : ofSaturation A ⟶ ofSaturation B),
      AffinoidAtlasPresentation.StrongHom.IsClosedImmersion (A := A) (B := B) g ∧
        Nonempty (Arrow.mk (localizationFunctor.map g) ≅ Arrow.mk φ)

/-- The image of a closed immersion between constructed saturations is a closed
immersion. -/
theorem closedImmersion_localizationFunctor_map {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (g : ofSaturation A ⟶ ofSaturation B)
    (hg : AffinoidAtlasPresentation.StrongHom.IsClosedImmersion (A := A) (B := B) g) :
    closedImmersion (localizationFunctor.map g) :=
  ⟨A, B, g, hg, ⟨Iso.refl _⟩⟩

/-- Closed immersions are stable under isomorphisms of arrows. -/
instance : (closedImmersion (K := K)).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e ⟨A, B, g, hg, ⟨e'⟩⟩ =>
    ⟨A, B, g, hg, ⟨e' ≪≫ e⟩⟩

/-- Every isomorphism of analytic spaces is a closed immersion. -/
theorem closedImmersion_of_isIso {X Y : LocalizedCategory.{u, v, v} (K := K)} (φ : X ⟶ Y)
    [IsIso φ] : closedImmersion φ := by
  obtain ⟨A, ⟨e⟩⟩ := exists_iso_localizationFunctor_obj_ofSaturation X
  refine ⟨A, A, 𝟙 _, AffinoidAtlasPresentation.StrongHom.isClosedImmersion_id A,
    ⟨Arrow.isoMk e (e ≪≫ asIso φ) ?_⟩⟩
  simp

/-- Identities are closed immersions. -/
instance : (closedImmersion (K := K)).ContainsIdentities where
  id_mem X := closedImmersion_of_isIso (𝟙 X)

section OpenImmersion

variable {X Y Z : LocalizedCategory.{u, v, w} (K := K)}

/-- Berkovich's open immersions: morphisms `φ : X ⟶ Y` inducing an isomorphism of `X`
with an open analytic domain of `Y`, that is, the composite of an isomorphism onto the
analytic space of an open subset `U` of `Y` with the canonical morphism of `U`. -/
def openImmersion : MorphismProperty (LocalizedCategory.{u, v, w} (K := K)) :=
  fun _ Y φ =>
    ∃ (U : Set (presentationOf Y).presentation.space) (hU : IsOpen U)
      (e : _ ≅ domainObj Y ((presentationOf Y).openDomain U hU)),
        e.hom ≫ domainι Y ((presentationOf Y).openDomain U hU) = φ

/-- The canonical morphism of an open domain is an open immersion. -/
theorem openImmersion_domainι (U : Set (presentationOf Y).presentation.space)
    (hU : IsOpen U) : openImmersion (domainι Y ((presentationOf Y).openDomain U hU)) :=
  ⟨U, hU, Iso.refl _, Category.id_comp _⟩

/-- The canonical morphism of an open domain is an open embedding of underlying
spaces. -/
theorem isOpenEmbedding_domainι (U : Set (presentationOf Y).presentation.space)
    (hU : IsOpen U) :
    IsOpenEmbedding
      (localizedSpaceFunctor.map (domainι Y ((presentationOf Y).openDomain U hU))) := by
  have h : ⇑(localizedSpaceFunctor.map (domainι Y ((presentationOf Y).openDomain U hU))) =
      Subtype.val (p := (· ∈ U)) :=
    funext (domainι_apply _)
  rw [h]
  exact hU.isOpenEmbedding_subtypeVal

/-- Open immersions are open embeddings of underlying spaces. -/
theorem openImmersion.isOpenEmbedding {φ : X ⟶ Y} (hφ : openImmersion φ) :
    IsOpenEmbedding (localizedSpaceFunctor.map φ) := by
  obtain ⟨U, hU, e, rfl⟩ := hφ
  rw [Functor.map_comp, TopCat.coe_comp]
  exact (isOpenEmbedding_domainι U hU).comp
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)).isOpenEmbedding

/-- The point map of the inverse of an isomorphism undoes the point map of the
isomorphism. -/
theorem map_inv_map_hom_apply (ψ : Y ≅ Z) (y : localizedSpaceFunctor.obj Y) :
    localizedSpaceFunctor.map ψ.inv (localizedSpaceFunctor.map ψ.hom y) = y :=
  Iso.hom_inv_id_apply (localizedSpaceFunctor.mapIso ψ) y

/-- An isomorphism `ψ : Y ≅ Z` identifies the open domain `U` of `Y` with the open
domain `ψ(U)` of `Z`, written as the preimage of `U` under the inverse. -/
def openDomainIso (ψ : Y ≅ Z) (U : Set (presentationOf Y).presentation.space)
    (hU : IsOpen U) :
    domainObj Y ((presentationOf Y).openDomain U hU) ≅
      domainObj Z ((presentationOf Z).openDomain (localizedSpaceFunctor.map ψ.inv ⁻¹' U)
        (hU.preimage (localizedSpaceFunctor.map ψ.inv).hom.continuous)) where
  hom := domainRestrict _ _ ψ.hom fun x hx =>
    (congrArg (· ∈ U) (map_inv_map_hom_apply ψ x)).mpr hx
  inv := domainRestrict _ _ ψ.inv fun _ hx => hx
  hom_inv_id := (cancel_mono (domainι Y _)).1 <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (domainRestrict_comp _ _ _ _)).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ ψ.inv) (domainRestrict_comp _ _ _ _)).trans <|
            (Category.assoc _ _ _).trans <|
              (congrArg (_ ≫ ·) ψ.hom_inv_id).trans <|
                (Category.comp_id _).trans (Category.id_comp _).symm
  inv_hom_id := (cancel_mono (domainι Z _)).1 <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (domainRestrict_comp _ _ _ _)).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ ψ.hom) (domainRestrict_comp _ _ _ _)).trans <|
            (Category.assoc _ _ _).trans <|
              (congrArg (_ ≫ ·) ψ.inv_hom_id).trans <|
                (Category.comp_id _).trans (Category.id_comp _).symm

/-- The identification of open domains commutes with the canonical morphisms. -/
@[reassoc (attr := simp)]
theorem openDomainIso_hom_domainι (ψ : Y ≅ Z) (U : Set (presentationOf Y).presentation.space)
    (hU : IsOpen U) :
    (openDomainIso ψ U hU).hom ≫ domainι Z _ = domainι Y _ ≫ ψ.hom :=
  domainRestrict_comp _ _ _ fun x hx => (congrArg (· ∈ U) (map_inv_map_hom_apply ψ x)).mpr hx

/-- Open immersions are stable under composition with isomorphisms on either side. -/
instance : (openImmersion : MorphismProperty (LocalizedCategory.{u, v, w} (K := K))).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ ⟨U, hU, e', h⟩ => ⟨U, hU, e ≪≫ e', by rw [Iso.trans_hom, Category.assoc, h]⟩)
    (fun ψ _ ⟨U, hU, e, h⟩ => ⟨_, _, e ≪≫ openDomainIso ψ U hU, by
      rw [Iso.trans_hom, Category.assoc, openDomainIso_hom_domainι, ← Category.assoc, h]⟩)

variable (X) in
/-- The identity is an open immersion, onto the open domain `univ`. -/
theorem openImmersion_id : openImmersion (𝟙 X) := by
  let D := (presentationOf X).openDomain Set.univ isOpen_univ
  have hD : ∀ x, localizedSpaceFunctor.map (𝟙 X) x ∈ D.carrier := fun _ => Set.mem_univ _
  refine ⟨Set.univ, isOpen_univ,
    { hom := domainLift D (𝟙 X) hD
      inv := domainι X D
      hom_inv_id := domainLift_comp D (𝟙 X) hD
      inv_hom_id := (cancel_mono (domainι X D)).1 <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (domainLift_comp D (𝟙 X) hD)).trans <|
            (Category.comp_id _).trans (Category.id_comp _).symm },
    domainLift_comp D (𝟙 X) hD⟩

/-- Identities are open immersions. -/
instance :
    (openImmersion :
      MorphismProperty (LocalizedCategory.{u, v, w} (K := K))).ContainsIdentities where
  id_mem X := openImmersion_id X

/-- Every isomorphism of analytic spaces is an open immersion. -/
theorem openImmersion_of_isIso (φ : X ⟶ Y) [IsIso φ] : openImmersion φ := by
  simpa using MorphismProperty.RespectsIso.postcomp openImmersion φ (𝟙 X) (openImmersion_id X)

end OpenImmersion

end SaturatedAtlasPresentation

end Langlands.Analytic
