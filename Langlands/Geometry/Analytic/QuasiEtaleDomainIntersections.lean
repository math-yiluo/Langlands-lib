import Langlands.Geometry.Analytic.QuasiEtaleDomainChartCover
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual intersections of compact quasi-étale domain charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Domains

variable {U : LocalizedCategory.{u, v, w} (K := K)}

/-- The actual map associated to inclusion of two ambient analytic domains. -/
def domainOrderMap {D E : (presentationOf U).AnalyticDomain} (h : D ≤ E) :
    domainObj U D ⟶ domainObj U E :=
  domainLift E (domainι U D) (fun x => by
    rw [domainι_apply]
    exact (show D.carrier ⊆ E.carrier from h) x.property)

@[reassoc (attr := simp)]
theorem domainOrderMap_comp_inclusion
    {D E : (presentationOf U).AnalyticDomain} (h : D ≤ E) :
    domainOrderMap h ≫ domainι U E = domainι U D :=
  domainLift_comp _ _ _

/-- Both actual intersection inclusions agree over the ambient space. -/
theorem domainIntersection_condition (D E : (presentationOf U).AnalyticDomain) :
    domainOrderMap (inf_le_left : D ⊓ E ≤ D) ≫ domainι U D =
      domainOrderMap (inf_le_right : D ⊓ E ≤ E) ≫ domainι U E := by
  simp only [domainOrderMap_comp_inclusion]

/-- A compatible pair of analytic arrows has image in the actual intersection. -/
theorem domainIntersection_image_mem
    (D E : (presentationOf U).AnalyticDomain)
    {Z : LocalizedCategory.{u, v, w} (K := K)}
    (a : Z ⟶ domainObj U D) (b : Z ⟶ domainObj U E)
    (h : a ≫ domainι U D = b ≫ domainι U E) :
    ∀ z, localizedSpaceFunctor.map (a ≫ domainι U D) z ∈ (D ⊓ E).carrier := by
  intro z
  have hz := congrArg (fun k => localizedSpaceFunctor.map k z) h
  simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at hz ⊢
  exact ⟨(localizedSpaceFunctor.map a z).property,
    hz ▸ (localizedSpaceFunctor.map b z).property⟩

/-- The universal actual analytic arrow into an intersection domain. -/
def domainIntersectionLift (D E : (presentationOf U).AnalyticDomain)
    {Z : LocalizedCategory.{u, v, w} (K := K)}
    (a : Z ⟶ domainObj U D) (b : Z ⟶ domainObj U E)
    (h : a ≫ domainι U D = b ≫ domainι U E) :
    Z ⟶ domainObj U (D ⊓ E) :=
  domainLift (D ⊓ E) (a ≫ domainι U D) (domainIntersection_image_mem D E a b h)

@[reassoc (attr := simp)]
theorem domainIntersectionLift_fst (D E : (presentationOf U).AnalyticDomain)
    {Z : LocalizedCategory.{u, v, w} (K := K)}
    (a : Z ⟶ domainObj U D) (b : Z ⟶ domainObj U E)
    (h : a ≫ domainι U D = b ≫ domainι U E) :
    domainIntersectionLift D E a b h ≫ domainOrderMap inf_le_left = a := by
  apply (cancel_mono (domainι U D)).1
  rw [Category.assoc, domainOrderMap_comp_inclusion]
  exact domainLift_comp _ _ _

@[reassoc (attr := simp)]
theorem domainIntersectionLift_snd (D E : (presentationOf U).AnalyticDomain)
    {Z : LocalizedCategory.{u, v, w} (K := K)}
    (a : Z ⟶ domainObj U D) (b : Z ⟶ domainObj U E)
    (h : a ≫ domainι U D = b ≫ domainι U E) :
    domainIntersectionLift D E a b h ≫ domainOrderMap inf_le_right = b := by
  apply (cancel_mono (domainι U E)).1
  rw [Category.assoc, domainOrderMap_comp_inclusion]
  exact (domainLift_comp _ _ _).trans h

/-- The intersection domain with its two actual analytic inclusions. -/
def domainIntersectionCone (D E : (presentationOf U).AnalyticDomain) :
    PullbackCone (domainι U D) (domainι U E) :=
  PullbackCone.mk (domainOrderMap inf_le_left) (domainOrderMap inf_le_right)
    (domainIntersection_condition D E)

/-- The universal property holds against every localized analytic test object. -/
def domainIntersectionIsLimit (D E : (presentationOf U).AnalyticDomain) :
    IsLimit (domainIntersectionCone D E) :=
  PullbackCone.IsLimit.mk (domainIntersection_condition D E)
    (fun c => domainIntersectionLift D E c.fst c.snd c.condition)
    (fun c => domainIntersectionLift_fst D E c.fst c.snd c.condition)
    (fun c => domainIntersectionLift_snd D E c.fst c.snd c.condition)
    (fun c m hm _ => (cancel_mono (domainι U (D ⊓ E))).1 (calc
      m ≫ domainι U (D ⊓ E) =
          (m ≫ domainOrderMap (inf_le_left : D ⊓ E ≤ D)) ≫ domainι U D := by
            rw [Category.assoc, domainOrderMap_comp_inclusion]
      _ = c.fst ≫ domainι U D := congrArg (· ≫ domainι U D) hm
      _ = _ := (domainLift_comp _ _ _).symm))

theorem domainIntersection_isPullback (D E : (presentationOf U).AnalyticDomain) :
    IsPullback (domainOrderMap (inf_le_left : D ⊓ E ≤ D))
      (domainOrderMap (inf_le_right : D ⊓ E ≤ E)) (domainι U D) (domainι U E) where
  w := domainIntersection_condition D E
  isLimit' := ⟨domainIntersectionIsLimit D E⟩

end Domains

section Factorizations

variable {U X : LocalizedCategory.{u, v, v} (K := K)}

/-- A smaller ambient domain inherits the larger domain's étale envelope. -/
theorem HasDomainEtaleFactorization.of_domain_le {f : U ⟶ X}
    {D E : (presentationOf U).AnalyticDomain}
    (hf : HasDomainEtaleFactorization (domainι U E ≫ f)) (h : D ≤ E) :
    HasDomainEtaleFactorization (domainι U D ≫ f) := by
  let F : (presentationOf (domainObj U E)).AnalyticDomain :=
    E.subspaceRestrict ⟨D, h⟩
  let e : domainObj (domainObj U E) F ≅ domainObj U (E.subspaceExtend F) :=
    domainNestedLocalizationIso (presentationOf U) E F
  have he : e.hom ≫ domainι U (E.subspaceExtend F) =
      domainι (domainObj U E) F ≫ domainι U E :=
    domainNestedLocalizationIso_hom_inclusion (presentationOf U) E F
  have h' := (hf.domainι_comp F).iso_comp e.symm
  have hw : domainι (domainObj U E) F ≫ (domainι U E ≫ f) =
      e.hom ≫ (domainι U (E.subspaceExtend F) ≫ f) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ f) he.symm).trans (Category.assoc _ _ _))
  rw [hw, Iso.symm_hom, Iso.inv_hom_id_assoc] at h'
  have hED : E.subspaceExtend F = D := E.subspaceExtend_subspaceRestrict ⟨D, h⟩
  exact Eq.mp (congrArg
    (fun Q : (presentationOf U).AnalyticDomain =>
      HasDomainEtaleFactorization (domainι U Q ≫ f)) hED) h'

end Factorizations

namespace FiniteCompactDomainChartCover

variable {X : LocalizedCategory.{u, v, v} (K := K)}
  {U : QuasiEtaleSite X} (C : FiniteCompactDomainChartCover U)

theorem isCompactSpace_domainObj (i : C.Index) :
    IsCompactSpace (domainObj U.left (C.domain i)) := by
  let : CompactSpace (localizedSpaceFunctor.obj (C.obj i).left) := (C.compact i).1
  let : T2Space (localizedSpaceFunctor.obj (C.obj i).left) := (C.compact i).2
  let e := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (C.domainIso i))
  exact ⟨e.compactSpace, e.t2Space⟩

theorem isCompact_domain (i : C.Index) : IsCompact (C.domain i).carrier :=
  isCompact_iff_compactSpace.mpr (C.isCompactSpace_domainObj i).1

/-- An anchored finite intersection includes the anchor even for an empty tail. -/
def intersectionDomain (i : C.Index) (s : Finset C.Index) :
    (presentationOf U.left).AnalyticDomain :=
  C.domain i ⊓ s.inf C.domain

theorem intersectionDomain_factorization (i : C.Index) (s : Finset C.Index) :
    HasDomainEtaleFactorization (domainι U.left (C.intersectionDomain i s) ≫ U.hom) :=
  (C.domain_factorization i).of_domain_le inf_le_left

theorem isClosed_finsetInf_domain [T2Space (localizedSpaceFunctor.obj U.left)]
    (s : Finset C.Index) : IsClosed (s.inf C.domain).carrier := by
  classical
  let : T2Space (presentationOf U.left).presentation.space :=
    ‹T2Space (localizedSpaceFunctor.obj U.left)›
  induction s using Finset.induction_on with
  | empty => exact isClosed_univ
  | @insert i s _ hs =>
    rw [Finset.inf_insert]
    change IsClosed ((C.domain i).carrier ∩ (s.inf C.domain).carrier)
    exact (C.isCompact_domain i).isClosed.inter hs

theorem isCompactSpace_intersectionObj [T2Space (localizedSpaceFunctor.obj U.left)]
    (i : C.Index) (s : Finset C.Index) :
    IsCompactSpace (domainObj U.left (C.intersectionDomain i s)) := by
  let : T2Space (presentationOf U.left).presentation.space :=
    ‹T2Space (localizedSpaceFunctor.obj U.left)›
  refine ⟨isCompact_iff_compactSpace.mp ?_,
    inferInstanceAs (T2Space (C.intersectionDomain i s).carrier)⟩
  exact (C.isCompact_domain i).inter_right (C.isClosed_finsetInf_domain s)

/-- A finite intersection is an actual quasi-étale site object over the base. -/
def intersectionObj (i : C.Index) (s : Finset C.Index) : QuasiEtaleSite X :=
  MorphismProperty.Over.mk ⊤
    (domainι U.left (C.intersectionDomain i s) ≫ U.hom)
    (C.intersectionDomain_factorization i s).quasiEtale

end FiniteCompactDomainChartCover

end Langlands.Analytic.SaturatedAtlasPresentation
