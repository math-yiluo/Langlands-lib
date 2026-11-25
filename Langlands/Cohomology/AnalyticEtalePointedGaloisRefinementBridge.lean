import Langlands.Cohomology.AnalyticEtaleGaloisCartanReduction
import Langlands.Geometry.Analytic.AnalyticGaloisCoverOpenRestriction
import Langlands.Geometry.Analytic.CompactEtaleNeighborhood
import Langlands.Geometry.Analytic.PointedAnalyticGaloisRefinement

/-! # Relative pointed refinement over the ambient analytic base -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology TopologicalSpace

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem domainIso_hom_inclusion_of_eq {A : LocalizedCategory.{u, v, v} (K := K)}
    {D E : (presentationOf A).AnalyticDomain} (h : D = E) :
    (eqToIso (congrArg (domainObj A) h)).hom ≫ domainι A E = domainι A D := by
  subst E
  simp

/-- When the inverse image of an open lies in a source domain, restriction to
the open agrees with restriction of the domain. -/
theorem exists_openRestrictionIso_within_domain
    {A X : LocalizedCategory.{u, v, v} (K := K)}
    (D : (presentationOf A).AnalyticDomain) (f : A ⟶ X)
    (U : Opens (localizedSpaceFunctor.obj X))
    (hD : localizedSpaceFunctor.map f ⁻¹' (U : Set (localizedSpaceFunctor.obj X)) ⊆ D.carrier) :
    let P := preimageOpenDomain f (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
    let Q := preimageOpenDomain (domainι A D ≫ f) (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
    ∃ e : domainObj A P ≅ domainObj (domainObj A D) Q,
      e.hom ≫ domainι (domainObj A D) Q ≫ domainι A D = domainι A P := by
  let P := preimageOpenDomain f (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  let q := domainι A D ≫ f
  let Q := preimageOpenDomain q (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  have hm (x : localizedSpaceFunctor.obj (domainObj A D)) :
      x ∈ Q.carrier ↔ localizedSpaceFunctor.map f x.val ∈ U := by
    change localizedSpaceFunctor.map q x ∈ U ↔ _
    rw [show q = domainι A D ≫ f from rfl, Functor.map_comp, TopCat.comp_app, domainι_apply]
  have h : D.subspaceExtend Q = P := by
    ext x
    change (∃ a : D.carrier, a ∈ Q.carrier ∧ a.val = x) ↔
      localizedSpaceFunctor.map f x ∈ U
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hm a).1 ha
    · intro hx
      exact ⟨⟨x, hD hx⟩, (hm ⟨x, hD hx⟩).2 hx, rfl⟩
  let i := domainNestedLocalizationIso (presentationOf A) D Q
  let e : domainObj A P ≅ domainObj (domainObj A D) Q :=
    eqToIso (congrArg (domainObj A) h.symm) ≪≫ i.symm
  refine ⟨e, ?_⟩
  have hi : i.hom ≫ domainι A (D.subspaceExtend Q) =
      domainι (domainObj A D) Q ≫ domainι A D :=
    domainNestedLocalizationIso_hom_inclusion (presentationOf A) D Q
  change ((eqToIso (congrArg (domainObj A) h.symm)).hom ≫ i.inv) ≫
    domainι (domainObj A D) Q ≫ domainι A D = _
  rw [← hi, Category.assoc, Iso.inv_hom_id_assoc]
  exact domainIso_hom_inclusion_of_eq h.symm

/-- The deck graph cover is unchanged after reidentifying its target. -/
def AnalyticGaloisCover.postcompIso
    {A X X' : LocalizedCategory.{u, v, v} (K := K)} {p : A ⟶ X}
    {Γ : Type z} [Group Γ] (c : AnalyticGaloisCover Γ p) (e : X ≅ X') :
    AnalyticGaloisCover Γ (p ≫ e.hom) := by
  have hdeck γ : (c.deck γ).asIso.hom ≫ (p ≫ e.hom) = p ≫ e.hom := by
    rw [← Category.assoc, c.deck_over]
  have hc : IsPullback c.fst c.snd (p ≫ e.hom) (p ≫ e.hom) :=
    c.isPullback.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp) (by simp)
  have hg (γ : Γ) :
      analyticDeckGraph hc (c.deck γ) (hdeck γ) = c.graph γ := by
    apply c.isPullback.hom_ext
    · rw [analyticDeckGraph, hc.lift_fst, c.graph_fst]
    · rw [analyticDeckGraph, hc.lift_snd, c.graph_snd]
  refine ⟨etale_comp c.etale_map (etale_of_isIso _), ?_, c.deck, hdeck,
    c.relation, c.fst, c.snd, hc, ?_, ?_⟩
  · rw [Functor.map_comp, TopCat.coe_comp]
    exact (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)).surjective.comp c.surjective
  · intro t
    simpa only [hg, AnalyticGaloisCover.graph] using c.covers t
  · intro γ δ h
    simpa only [hg, AnalyticGaloisCover.graph] using c.disjoint_graphs h

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Sheaf.Equivariant.Analytic.EtaleGermNeighborhood

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {y : localizedSpaceFunctor.obj X}
variable (P : EtaleGermNeighborhood X y)

/-- An open immersion through the marked point inherits cofinal base neighbourhoods. -/
def ofOpenImmersion {A : EtaleSite X} (f : A ⟶ P.obj) (hf : openImmersion f.left)
    (x : localizedSpaceFunctor.obj A.left)
    (hx : localizedSpaceFunctor.map f.left x = P.point) :
    EtaleGermNeighborhood X y := by
  have h (a : localizedSpaceFunctor.obj A.left) :
      localizedSpaceFunctor.map P.obj.hom (localizedSpaceFunctor.map f.left a) =
        localizedSpaceFunctor.map A.hom a :=
    (localizedSpaceFunctor.map_comp_apply f.left P.obj.hom a).symm.trans
      (congrArg (fun k => localizedSpaceFunctor.map k a) (MorphismProperty.Over.w f))
  refine ⟨A, x, (h x).symm.trans ((congrArg (localizedSpaceFunctor.map P.obj.hom) hx).trans
    P.map_point), ?_⟩
  intro U hxU
  let V : Opens (localizedSpaceFunctor.obj P.obj.left) :=
    ⟨localizedSpaceFunctor.map f.left '' (U : Set (localizedSpaceFunctor.obj A.left)),
      hf.isOpenEmbedding.isOpenMap _ U.isOpen⟩
  obtain ⟨B, hyB, hB⟩ := P.shrink V ⟨x, hxU, hx⟩
  refine ⟨B, hyB, fun a ha => ?_⟩
  have ha' : localizedSpaceFunctor.map P.obj.hom (localizedSpaceFunctor.map f.left a) ∈ B :=
    (congrArg (fun t => t ∈ B) (h a)).mpr ha
  obtain ⟨b, hb, he⟩ := hB ha'
  exact hf.isOpenEmbedding.injective he ▸ hb

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ρ : G →* Aut X}
variable [T2Space (localizedSpaceFunctor.obj X)]

/-- A pointed neighbourhood admits a distinguished base restriction inside any
prescribed neighbourhood. -/
theorem exists_distinguished_restriction (hρ : IsContinuousAction ρ)
    (N : Opens (localizedSpaceFunctor.obj X)) (hyN : y ∈ N) :
    ∃ (U : Opens (localizedSpaceFunctor.obj X)) (hyU : y ∈ U),
      U ≤ N ∧ IsDistinguishedEtale (P.restrict U hyU).obj.hom := by
  obtain ⟨D, B, hD, hpt, _, hpB, hBO⟩ :=
    (compactEtaleNeighborhood (K := K)) P.obj.prop P.point univ Filter.univ_mem
  change Opens (localizedSpaceFunctor.obj X) at B
  let C : Opens (localizedSpaceFunctor.obj P.obj.left) :=
    ⟨D.carrier ∩ localizedSpaceFunctor.map P.obj.hom ⁻¹' (B : Set (localizedSpaceFunctor.obj X)),
      hBO⟩
  obtain ⟨O, hyO, hO⟩ := P.shrink C ⟨hpt, hpB⟩
  have hON : y ∈ (O ⊓ N : Opens _) := ⟨hyO, hyN⟩
  obtain ⟨V, _, hV, hyV, hsub, _, _⟩ := hasStableDistinguishedOpenNeighborhoods hρ y
    ((O ⊓ N : Opens _) : Set _) (O ⊓ N).isOpen hON
  let U : Opens (localizedSpaceFunctor.obj X) := ⟨V, hV.1⟩
  have hU : U ≤ O ⊓ N := subset_closure.trans hsub
  have hUD : localizedSpaceFunctor.map P.obj.hom ⁻¹' (U : Set (localizedSpaceFunctor.obj X)) ⊆
      D.carrier :=
    fun a ha => (hO ((hU.trans inf_le_left) ha)).1
  obtain ⟨e, he⟩ := exists_openRestrictionIso_within_domain D P.obj.hom U hUD
  let W := domainObj P.obj.left D
  let f := domainι P.obj.left D ≫ P.obj.hom
  let E := preimageOpenDomain f (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  let F := domainPreimage f (⟨Vᶜ, hV.2⟩ : (presentationOf X).AnalyticDomain)
  refine ⟨U, hyV, hU.trans inf_le_right, (P.restrict U hyV).obj.prop,
    W, f, quasiEtale_domainι_comp_of_etale D P.obj.hom P.obj.prop, hD, E, F,
    U.isOpen.preimage (localizedSpaceFunctor.map f).hom.continuous, rfl, e, ?_⟩
  have h := MorphismProperty.Over.w ((etaleOpenRestrictionInclusion X U).app P.obj)
  refine h.symm.trans ?_
  change domainι P.obj.left (preimageOpenDomain P.obj.hom
    (U : Set (localizedSpaceFunctor.obj X)) U.isOpen) ≫ P.obj.hom =
      e.hom ≫ domainι W E ≫ f
  change e.hom ≫ domainι W E ≫ domainι P.obj.left D =
    domainι P.obj.left (preimageOpenDomain P.obj.hom
      (U : Set (localizedSpaceFunctor.obj X)) U.isOpen) at he
  have hcomp := congrArg (fun g => g ≫ P.obj.hom) he.symm
  simp only [Category.assoc] at hcomp
  exact hcomp

end Langlands.Sheaf.Equivariant.Analytic.EtaleGermNeighborhood

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} [T2Space (localizedSpaceFunctor.obj X)]
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ρ : G →* Aut X}

/-- Restrict a pointed relative Galois refinement to an ambient base open
on which its source is distinguished. -/
theorem exists_ambientGaloisRefinement (hρ : IsContinuousAction ρ)
    {y : localizedSpaceFunctor.obj X} (V : EtaleGermNeighborhood X y)
    {W : EtaleSite X} (f : W ⟶ V.obj) (C : PointedAnalyticGaloisRefinement f.left V.point) :
    ∃ (E : EtaleGermGaloisCover V) (g : E.source.obj ⟶ W), g ≫ f = E.toBase := by
  let D := (presentationOf V.obj.left).openDomain
    (C.baseOpen : Set (localizedSpaceFunctor.obj V.obj.left)) C.baseOpen.isOpen
  let V₀ : EtaleSite X := MorphismProperty.Over.mk ⊤ (domainι V.obj.left D ≫ V.obj.hom)
    (etale_comp (etaleOpenDomainStatement V.obj.left _ C.baseOpen.isOpen) V.obj.prop)
  let i : V₀ ⟶ V.obj := MorphismProperty.Over.homMk (domainι V.obj.left D) rfl
  have hfactor : C.lift ≫ f.left = C.p ≫ i.left := C.factors
  let x₀ : localizedSpaceFunctor.obj V₀.left := ⟨V.point, C.mem_baseOpen⟩
  let P₀ := V.ofOpenImmersion i (openImmersion_domainι _ C.baseOpen.isOpen) x₀ rfl
  let A : EtaleSite X := MorphismProperty.Over.mk ⊤ (C.p ≫ V₀.hom)
    (etale_comp C.geometry.etale_map V₀.prop)
  let p : A ⟶ P₀.obj := MorphismProperty.Over.homMk C.p rfl
  let P := P₀.ofProper p C.geometry.isProperMap C.point C.map_point C.unique_point
  obtain ⟨N, hyN, hN⟩ := V.shrink C.baseOpen C.mem_baseOpen
  obtain ⟨U, hyU, hUN, hdist⟩ := P.exists_distinguished_restriction hρ N hyN
  have hU : localizedSpaceFunctor.map V.obj.hom ⁻¹' (U : Set (localizedSpaceFunctor.obj X)) ⊆
      D.carrier := fun x hx => hN (hUN hx)
  obtain ⟨e, he⟩ := exists_openRestrictionIso_within_domain D V.obj.hom U hU
  let T : Opens (localizedSpaceFunctor.obj V₀.left) :=
    ⟨localizedSpaceFunctor.map V₀.hom ⁻¹' (U : Set (localizedSpaceFunctor.obj X)),
      U.isOpen.preimage (localizedSpaceFunctor.map V₀.hom).hom.continuous⟩
  let D' := preimageOpenDomain C.p (T : Set (localizedSpaceFunctor.obj V₀.left)) T.isOpen
  let a := domainι A.left D'
  have ho : IsOpen D'.carrier := T.isOpen.preimage (localizedSpaceFunctor.map C.p).hom.continuous
  let A' : EtaleSite X := MorphismProperty.Over.mk ⊤ (a ≫ A.hom)
    (etale_comp (etaleOpenDomainStatement A.left D'.carrier ho) A.prop)
  have hD' : D' = preimageOpenDomain A.hom (U : Set (localizedSpaceFunctor.obj X)) U.isOpen := by
    ext x
    change localizedSpaceFunctor.map V₀.hom (localizedSpaceFunctor.map C.p x) ∈ U ↔
      localizedSpaceFunctor.map (C.p ≫ V₀.hom) x ∈ U
    exact (congrArg (fun z => z ∈ U) (localizedSpaceFunctor.map_comp_apply C.p V₀.hom x)).symm.to_iff
  have hdist' : IsDistinguishedEtale A'.hom := by
    have h : (P.restrict U hyU).obj.hom =
        domainι A.left (preimageOpenDomain A.hom (U : Set (localizedSpaceFunctor.obj X)) U.isOpen) ≫
          A.hom := (MorphismProperty.Over.w ((etaleOpenRestrictionInclusion X U).app A)).symm
    change IsDistinguishedEtale (domainι A.left D' ≫ A.hom)
    rw [hD', ← h]
    exact hdist
  have hx : localizedSpaceFunctor.map C.p C.point ∈ T := by
    change localizedSpaceFunctor.map V₀.hom (localizedSpaceFunctor.map C.p C.point) ∈ U
    have h : localizedSpaceFunctor.map V₀.hom (localizedSpaceFunctor.map C.p C.point) = y :=
      (localizedSpaceFunctor.map_comp_apply C.p V₀.hom C.point).symm.trans P.map_point
    exact (congrArg (fun x => x ∈ U) h).mpr hyU
  let x' : localizedSpaceFunctor.obj A'.left := ⟨C.point, hx⟩
  let a' : A' ⟶ P.obj := MorphismProperty.Over.homMk a rfl
  have ha' : openImmersion a'.left := openImmersion_domainι D'.carrier ho
  let P' := P.ofOpenImmersion a' ha' x' rfl
  let b := preimageOpenDomainMap C.p (T : Set (localizedSpaceFunctor.obj V₀.left)) T.isOpen
  let j := domainι V₀.left ((presentationOf V₀.left).openDomain
    (T : Set (localizedSpaceFunctor.obj V₀.left)) T.isOpen)
  let k := restrictEtaleInclusion X U V.obj
  have hb : b ≫ j = a ≫ C.p := preimageOpenDomainMap_comp _ _ _
  have he' : e.inv ≫ k = j ≫ i.left := by
    have h : e.hom ≫ j ≫ i.left = k := he
    rw [← h, Iso.inv_hom_id_assoc]
  let r : P'.obj ⟶ (V.restrict U hyU).obj :=
    MorphismProperty.Over.homMk (b ≫ e.inv) (by
      have hk : (V.restrict U hyU).obj.hom = k ≫ V.obj.hom :=
        (MorphismProperty.Over.w ((etaleOpenRestrictionInclusion X U).app V.obj)).symm
      refine (congrArg (fun g => (b ≫ e.inv) ≫ g) hk).trans ?_
      change (b ≫ e.inv) ≫ k ≫ V.obj.hom = a ≫ C.p ≫ i.left ≫ V.obj.hom
      simp only [Category.assoc, reassoc_of% he', reassoc_of% hb])
  let g : P'.obj ⟶ W := MorphismProperty.Over.homMk (a ≫ C.lift) (by
    change (a ≫ C.lift) ≫ W.hom = a ≫ C.p ≫ i.left ≫ V.obj.hom
    rw [← MorphismProperty.Over.w f]
    simp only [Category.assoc, reassoc_of% hfactor])
  let E : EtaleGermGaloisCover V :=
    { baseOpen := U
      mem_baseOpen := hyU
      source := P'
      Γ := C.Γ
      p := r
      geometry := (C.geometry.restrictOpen T).postcompIso e.symm
      distinguished := hdist' }
  refine ⟨E, g, MorphismProperty.Over.Hom.ext ?_⟩
  change (a ≫ C.lift) ≫ f.left = (b ≫ e.inv) ≫ k
  simp only [Category.assoc, hfactor, he', reassoc_of% hb]

/-- The relative pointed refinement statement gives the geometric premise
of the analytic Galois–Cartan reduction. -/
theorem hasPointedEtaleGaloisRefinements_of_relative (hρ : IsContinuousAction ρ)
    (h : PointedAnalyticGaloisRefinementStatement.{u, v} K) :
    HasPointedEtaleGaloisRefinements X := by
  intro y V W f x hx
  obtain ⟨C⟩ := h f.left (EtaleSite.etale_left f) x
  exact exists_ambientGaloisRefinement hρ V f (hx ▸ C)

omit [T2Space (localizedSpaceFunctor.obj X)] in
/-- Relative pointed Galois refinement implies the analytic local acyclicity statement. -/
theorem analyticEtaleGaloisCoinducedLocalAcyclic_of_relativeRefinement
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (R : Type (max u (v + 1) uL)) [CommRing R] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (h : PointedAnalyticGaloisRefinementStatement.{u, v} K) :
    AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ := by
  intro hX hρ
  have : T2Space (localizedSpaceFunctor.obj X) := hX
  exact analyticEtaleGaloisCoinducedLocalAcyclic_of_pointedRefinements R L
    (hasPointedEtaleGaloisRefinements_of_relative hρ h) hX hρ

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
