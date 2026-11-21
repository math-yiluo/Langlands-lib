import Langlands.Geometry.Analytic.QuasiEtaleCompPrerequisites
import Langlands.Geometry.Analytic.QuasiEtaleDomainIntersections
import Langlands.Geometry.Analytic.QuasiEtaleDomains
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.CompactQuasiEtaleDiagonalPullbacks

/-! # Composition of quasi-étale morphisms from local domain–étale factorizations -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The restriction `w⁻¹(D) → D` of an étale morphism over an analytic domain
`D` of its target is étale: it is a base change of `w`. -/
theorem etale_domainPreimageMap {W X : LocalizedCategory.{u, v, v} (K := K)} (w : W ⟶ X)
    (D : (presentationOf X).AnalyticDomain) (hw : etale w) :
    etale (domainPreimageMap w D) := by
  obtain ⟨P, p, q, hP, hq⟩ :=
    localizedEtalePullbackBaseChange (K := K) w (domainι X D) hw
  have h := domainPreimage_isPullback w D
  have e : (h.isoIsPullback _ _ hP).hom ≫ q = domainPreimageMap w D :=
    h.isoIsPullback_hom_snd _ _ hP
  rw [← e]
  exact (MorphismProperty.cancel_left_of_respectsIso (etale (K := K)) _ q).2 hq

/-- A domain–étale factorization followed by an étale morphism is again one. -/
theorem HasDomainEtaleFactorization.comp_etale {U X Y : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ X} (hf : HasDomainEtaleFactorization f) {h : X ⟶ Y} (hh : etale h) :
    HasDomainEtaleFactorization (f ≫ h) := by
  obtain ⟨W, j, g, hj, hg, rfl⟩ := hf
  exact ⟨W, j, g ≫ h, hj, etale_comp hg hh, (Category.assoc _ _ _).symm⟩

/-- Local domain–étale factorizations persist after an étale morphism. -/
theorem HasLocalDomainEtaleFactorizations.comp_etale
    {U X Y : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}
    (hf : HasLocalDomainEtaleFactorizations f) {h : X ⟶ Y} (hh : etale h) :
    HasLocalDomainEtaleFactorizations (f ≫ h) := by
  intro y
  obtain ⟨C, hC, hn, hD⟩ := hf y
  refine ⟨C, hC, hn, fun D hDC => ⟨(hD D hDC).1, ?_⟩⟩
  have h' := (hD D hDC).2.comp_etale hh
  rwa [Category.assoc] at h'

section Nested

variable {U X : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}
  {P : (presentationOf U).AnalyticDomain} {E : (presentationOf (domainObj U P)).AnalyticDomain}

/-- The nested-domain comparison, with both objects written as domain objects. -/
private def nestedIso : domainObj (domainObj U P) E ≅ domainObj U (P.subspaceExtend E) :=
  domainNestedLocalizationIso (presentationOf U) P E

private theorem nestedIso_comp :
    (nestedIso (P := P) (E := E)).hom ≫ domainι U (P.subspaceExtend E) ≫ f =
      domainι (domainObj U P) E ≫ domainι U P ≫ f :=
  domainNestedLocalizationIso_hom_inclusion_assoc (presentationOf U) P E f

/-- A factorization of a domain of a domain gives one of its ambient image. -/
theorem HasDomainEtaleFactorization.subspaceExtend
    (h : HasDomainEtaleFactorization (domainι (domainObj U P) E ≫ domainι U P ≫ f)) :
    HasDomainEtaleFactorization (domainι U (P.subspaceExtend E) ≫ f) := by
  rw [← nestedIso_comp] at h
  have h' := h.iso_comp (nestedIso (P := P) (E := E)).symm
  rwa [Iso.symm_hom, Iso.inv_hom_id_assoc] at h'

end Nested

/-- A morphism into an analytic domain is an analytic-domain embedding as soon
as its composite with the inclusion of the domain is one. -/
theorem IsAnalyticDomainEmbedding.of_comp_domainι
    {V W : LocalizedCategory.{u, v, v} (K := K)}
    {P : (presentationOf W).AnalyticDomain} {n : V ⟶ domainObj W P}
    (h : IsAnalyticDomainEmbedding (n ≫ domainι W P)) : IsAnalyticDomainEmbedding n := by
  obtain ⟨D, e, he⟩ := h
  have hDP : D ≤ P := by
    intro x hx
    let hₑ := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
    let p : localizedSpaceFunctor.obj (domainObj W D) := ⟨x, hx⟩
    have h1 : localizedSpaceFunctor.map (n ≫ domainι W P) (hₑ.symm p) = x := by
      rw [he, Functor.map_comp, TopCat.comp_app, domainι_apply]
      change (hₑ (hₑ.symm p)).val = x
      rw [hₑ.apply_symm_apply]
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply] at h1
    rw [← h1]
    exact (localizedSpaceFunctor.map n (hₑ.symm p)).property
  let D' : (presentationOf (domainObj W P)).AnalyticDomain := P.subspaceRestrict ⟨D, hDP⟩
  have hE : P.subspaceExtend D' = D := P.subspaceExtend_subspaceRestrict ⟨D, hDP⟩
  let N : domainObj (domainObj W P) D' ≅ domainObj W (P.subspaceExtend D') :=
    domainNestedLocalizationIso (presentationOf W) P D'
  let d : domainObj W (P.subspaceExtend D') ≅ domainObj W D :=
    eqToIso (congrArg (fun F => localizationFunctor.obj ((presentationOf W).domain F)) hE)
  have hN : N.hom ≫ domainι W (P.subspaceExtend D') =
      domainι (domainObj W P) D' ≫ domainι W P :=
    domainNestedLocalizationIso_hom_inclusion (presentationOf W) P D'
  have hd : d.hom ≫ domainι W D = domainι W (P.subspaceExtend D') :=
    eqToIso_hom_domainInclusion (presentationOf W) hE
  refine ⟨D', e ≪≫ d.symm ≪≫ N.symm, ?_⟩
  apply (cancel_mono (domainι W P)).1
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← hN, Iso.inv_hom_id_assoc, ← hd, Iso.inv_hom_id_assoc]

/-- Local domain–étale factorizations persist after precomposition with an
analytic-domain embedding. -/
theorem HasLocalDomainEtaleFactorizations.analyticDomainEmbedding_comp
    {V U X : LocalizedCategory.{u, v, v} (K := K)} {n : V ⟶ U} {f : U ⟶ X}
    (hf : HasLocalDomainEtaleFactorizations f) (hn : IsAnalyticDomainEmbedding n) :
    HasLocalDomainEtaleFactorizations (n ≫ f) := by
  obtain ⟨Q, e, rfl⟩ := hn
  refine (hf.domainι_comp Q).of_iso e (Iso.refl X) ?_
  simp only [Iso.refl_hom, Category.comp_id, Category.assoc]

/-- Local domain–étale factorizations of the restrictions to a finite
neighbourhood of analytic domains through each point give them for the
morphism itself. -/
theorem HasLocalDomainEtaleFactorizations.of_domain_cover
    {U X : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}
    (h : ∀ y : localizedSpaceFunctor.obj U, ∃ C : Set (presentationOf U).AnalyticDomain,
      C.Finite ∧ (⋃ D ∈ C, D.carrier) ∈ 𝓝 y ∧
        ∀ D ∈ C, y ∈ D.carrier ∧ HasLocalDomainEtaleFactorizations (domainι U D ≫ f)) :
    HasLocalDomainEtaleFactorizations f := by
  classical
  intro y
  obtain ⟨C, hC, hn, hD⟩ := h y
  have hlocal : ∀ D ∈ C, ∃ E : Set (presentationOf U).AnalyticDomain, E.Finite ∧
      (∀ F ∈ E, y ∈ F.carrier ∧ HasDomainEtaleFactorization (domainι U F ≫ f)) ∧
      ∃ O ∈ 𝓝 y, O ∩ D.carrier ⊆ ⋃ F ∈ E, F.carrier := by
    intro D hDC
    obtain ⟨hyD, hfD⟩ := hD D hDC
    let yD : localizedSpaceFunctor.obj (domainObj U D) := ⟨y, hyD⟩
    obtain ⟨E, hE, hEn, hEf⟩ := hfD yD
    obtain ⟨O, hO, hsub⟩ := (mem_nhds_subtype D.carrier yD _).mp hEn
    refine ⟨D.subspaceExtend '' E, hE.image _, ?_, O, hO, ?_⟩
    · rintro _ ⟨F, hF, rfl⟩
      obtain ⟨hyF, hfF⟩ := hEf F hF
      exact ⟨⟨yD, hyF, rfl⟩, hfF.subspaceExtend⟩
    · rintro x ⟨hxO, hxD⟩
      obtain ⟨F, hF, hxF⟩ := mem_iUnion₂.mp (hsub (a := ⟨x, hxD⟩) hxO)
      exact mem_iUnion₂.mpr ⟨D.subspaceExtend F, ⟨F, hF, rfl⟩, ⟨⟨x, hxD⟩, hxF, rfl⟩⟩
  choose E hE hEf O hO hOE using hlocal
  let : Finite C := hC.to_subtype
  refine ⟨⋃ D : C, E D.val D.property, Set.finite_iUnion fun D => hE D.val D.property, ?_, ?_⟩
  · have hOn : (⋂ D : C, O D.val D.property) ∈ 𝓝 y :=
      Filter.iInter_mem.mpr fun D => hO D.val D.property
    refine Filter.mem_of_superset (Filter.inter_mem hn hOn) ?_
    rintro x ⟨hx, hOx⟩
    obtain ⟨D, hDC, hxD⟩ := mem_iUnion₂.mp hx
    have hxO := mem_iInter.mp hOx (⟨D, hDC⟩ : C)
    obtain ⟨F, hF, hxF⟩ := mem_iUnion₂.mp (hOE D hDC ⟨hxO, hxD⟩)
    exact mem_iUnion₂.mpr ⟨F, mem_iUnion.mpr ⟨⟨D, hDC⟩, hF⟩, hxF⟩
  · intro F hF
    obtain ⟨D, hF⟩ := mem_iUnion.mp hF
    exact hEf D.val D.property F hF

/-- The local step: if `f` restricted to `D` and `g` restricted to `E` have
domain–étale factorizations, then `f ≫ g` restricted to `D ∩ f⁻¹(E)` has local
domain–étale factorizations. -/
theorem hasLocalDomainEtaleFactorizations_inf_domainPreimage
    (hA : QuasiEtaleLocalDomainFactorizationsStatement.{u, v} K)
    (hB : EtaleDomainQuasiEtaleStatement.{u, v} K)
    {A B C : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ B} {g : B ⟶ C}
    {D : (presentationOf A).AnalyticDomain} {E : (presentationOf B).AnalyticDomain}
    (hD : HasDomainEtaleFactorization (domainι A D ≫ f))
    (hE : HasDomainEtaleFactorization (domainι B E ≫ g)) :
    HasLocalDomainEtaleFactorizations (domainι A (D ⊓ domainPreimage f E) ≫ f ≫ g) := by
  obtain ⟨W, j, w, hj, hw, hjw⟩ := hD
  obtain ⟨W', j', w', ⟨R, e', rfl⟩, hw', hjw'⟩ := hE
  let P := domainPreimage w E
  let p := domainPreimageMap w E
  have hp : etale (p ≫ e'.hom) := etale_comp (etale_domainPreimageMap w E hw) (etale_of_isIso _)
  have hP : HasLocalDomainEtaleFactorizations (domainι W P ≫ w ≫ g) := by
    have h1 := (hA _ (hB R _ hp)).comp_etale hw'
    have h2 : ((p ≫ e'.hom) ≫ domainι W' R) ≫ w' = domainι W P ≫ w ≫ g := by
      rw [Category.assoc, Category.assoc, ← Category.assoc e'.hom, hjw',
        domainPreimageMap_comp_inclusion_assoc]
    rwa [h2] at h1
  let G := D ⊓ domainPreimage f E
  let m : domainObj A G ⟶ domainObj A D := domainOrderMap (inf_le_left : G ≤ D)
  have hm : IsAnalyticDomainEmbedding m := by
    apply IsAnalyticDomainEmbedding.of_comp_domainι
    rw [domainOrderMap_comp_inclusion]
    exact isAnalyticDomainEmbedding_domainι A G
  have hmem : ∀ x, localizedSpaceFunctor.map (m ≫ j) x ∈ P.carrier := by
    intro x
    change localizedSpaceFunctor.map w (localizedSpaceFunctor.map (m ≫ j) x) ∈ E.carrier
    rw [← TopCat.comp_app, ← Functor.map_comp, Category.assoc, hjw, ← Category.assoc,
      domainOrderMap_comp_inclusion, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact x.property.2
  let n : domainObj A G ⟶ domainObj W P := domainLift P (m ≫ j) hmem
  have hn : n ≫ domainι W P = m ≫ j := domainLift_comp _ _ _
  have hna : IsAnalyticDomainEmbedding n := by
    apply IsAnalyticDomainEmbedding.of_comp_domainι
    rw [hn]
    exact hm.comp hj
  have h3 := hP.analyticDomainEmbedding_comp hna
  have hmD : m ≫ domainι A D = domainι A G := domainOrderMap_comp_inclusion _
  have h4 : n ≫ domainι W P ≫ w ≫ g = domainι A G ≫ f ≫ g := by
    rw [← Category.assoc n, hn, Category.assoc, reassoc_of% hjw, ← Category.assoc m, hmD]
  rwa [h4] at h3

/-- Proof of `QuasiEtaleCompReductionStatement`: local domain–étale
factorizations of quasi-étale morphisms and quasi-étaleness of étale morphisms
into analytic domains imply that quasi-étale morphisms compose. -/
theorem quasiEtaleCompReduction : QuasiEtaleCompReductionStatement.{u, v} K := by
  intro hA hB
  refine ⟨fun {A B C} f g hf hg => ?_⟩
  apply HasLocalDomainEtaleFactorizations.quasiEtale
  apply HasLocalDomainEtaleFactorizations.of_domain_cover
  intro y
  obtain ⟨CD, hCD, hnD, hD⟩ := hA f hf y
  obtain ⟨CE, hCE, hnE, hE⟩ := hA g hg (localizedSpaceFunctor.map f y)
  refine ⟨Set.image2 (fun D E => D ⊓ domainPreimage f E) CD CE, hCD.image2 _ hCE, ?_, ?_⟩
  · refine Filter.mem_of_superset (Filter.inter_mem hnD
      ((localizedSpaceFunctor.map f).hom.continuous.continuousAt.preimage_mem_nhds hnE)) ?_
    rintro x ⟨hxD, hxE⟩
    obtain ⟨D, hDC, hxD⟩ := mem_iUnion₂.mp hxD
    obtain ⟨E, hEC, hxE⟩ := mem_iUnion₂.mp hxE
    exact mem_iUnion₂.mpr ⟨_, ⟨D, hDC, E, hEC, rfl⟩, ⟨hxD, hxE⟩⟩
  · rintro _ ⟨D, hDC, E, hEC, rfl⟩
    obtain ⟨hyD, hfD⟩ := hD D hDC
    obtain ⟨hyE, hgE⟩ := hE E hEC
    exact ⟨⟨hyD, hyE⟩, hasLocalDomainEtaleFactorizations_inf_domainPreimage hA hB hfD hgE⟩

end Langlands.Analytic.SaturatedAtlasPresentation
