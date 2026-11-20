import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartCover
import Langlands.Geometry.Analytic.SpaceAnalytificationOpenImmersionPreservation

/-! # Preservation of open immersions by affinoid tests -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
  {p' : PointFamily K X' Y'} {p : PointFamily K X Y}

set_option backward.isDefEq.respectTransparency false in
/-- A compatible analytification map of an algebraic monomorphism is monic. -/
theorem mono_of_mono_hom (f : X' ⟶ X) [Mono (hom f)] (F : Y' ⟶ Y)
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (hX' : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
    (hX : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x)) : Mono F := by
  constructor
  intro S l m hlm
  obtain ⟨S₀, hS⟩ := localizedObjectEquiv.surjective S
  change localizationFunctor.obj S₀ = S at hS
  subst S
  obtain ⟨A, e, I, hI, h⟩ := exists_affinoidPointHom_pair_chartCover
    hp' hp' hX' hX'ft hX' hX'ft S₀ l m
  apply (cancel_epi e.hom).mp
  apply localizedHom_ext_of_chartCover (fun i : I => i.val) hI
  intro i
  obtain ⟨x, y, hx, hy⟩ := h i
  have hxy : RingPoints.map f x = RingPoints.map f y := by
    apply affinoidPointHom_injective hp hX hXft
    rw [← affinoidPointHom_comp hp' hX' hX'ft hp hX hXft f F hF _ x,
      ← affinoidPointHom_comp hp' hX' hX'ft hp hX hXft f F hF _ y,
      hx, hy]
    simp only [Category.assoc, hlm]
  have heq : x = y := by
    apply (uliftYonedaEquiv.{u + 1}).symm.injective
    apply (cancel_mono (hom f)).mp
    change pointHom K x ≫ hom f = pointHom K y ≫ hom f
    rw [← pointHom_map, ← pointHom_map, hxy]
  exact hx.symm.trans (heq ▸ hy)

set_option backward.isDefEq.respectTransparency false in
/-- A map of two supplied analytifications of the same algebraic space
that agrees on their affine tests is the hom of an isomorphism. -/
def compatibleAnalytificationIso
    {Z : LocalizedCategory.{u, u, u} (K := K)} {q : PointFamily K X Z}
    (hp : IsAnalytification K X Y p) (hq : IsAnalytification K X Z q)
    (hs : IsSeparated X) (ht : LocallyOfFiniteTypeOverBase X) (g : Y ⟶ Z)
    (hg : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X A),
      p A P x ≫ g = q A P x) : {e : Y ≅ Z // e.hom = g} := by
  let : Mono (hom (𝟙 X)) := by
    change Mono (𝟙 X.presheaf)
    infer_instance
  have hgid (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X A) :
      p A P x ≫ g = q A P (RingPoints.map (𝟙 X) x) := by
    rw [RingPoints.map_id]
    exact hg A P x
  let : Mono g := mono_of_mono_hom (𝟙 X) g hp hq hs ht hs ht hgid
  have hsplit : ∃ b : Z ⟶ Y, b ≫ g = 𝟙 Z := by
    obtain ⟨S, hS⟩ := localizedObjectEquiv.surjective Z
    change localizationFunctor.obj S = Z at hS
    subst Z
    obtain ⟨A, e, I, hI, h⟩ := exists_affinoidPointHom_pair_chartCover
      hq hq hs ht hs ht S (𝟙 _) (𝟙 _)
    have hl (i : I) : ∃ b : localizationFunctor.obj (A.smallChartSpectrum i.val) ⟶ Y,
        b ≫ g = localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom := by
      obtain ⟨x, _, hx, _⟩ := h i
      refine ⟨affinoidPointHom hp hs ht _ x, ?_⟩
      rw [affinoidPointHom_comp hp hs ht hq hs ht (𝟙 X) g hgid,
        RingPoints.map_id, hx, Category.comp_id]
    obtain ⟨b, hb, -⟩ := exists_lift_of_chartCover (fun i : I => i.val) hI g g
      (fun _ _ _ h _ => (cancel_mono g).mp h) e.hom e.hom (fun i => by
        obtain ⟨b, hb⟩ := hl i
        exact ⟨b, hb, hb⟩)
    exact ⟨e.inv ≫ b, by rw [Category.assoc, hb, Iso.inv_hom_id]⟩
  let b := hsplit.choose
  have hb : b ≫ g = 𝟙 Z := hsplit.choose_spec
  refine ⟨⟨g, b, (cancel_mono g).mp ?_, hb⟩, rfl⟩
  rw [Category.assoc, hb, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Analytification carries an algebraic open immersion to an isomorphism
onto its open analytic image. -/
theorem openImmersion_of_isOpenImmersion (f : X' ⟶ X) (F : Y' ⟶ Y)
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (hX' : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    (hf : AlgebraicSpace.IsOpenImmersion (hom f)) : openImmersion F := by
  let g (i : EtaleAffineTest K X') := p' i.algebra i.presentation i.point
  have hfEtale := PointOpenSubspace.isEtale_of_isOpenImmersion hf
  have hEtale (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A)
      (hx : AlgebraicSpace.IsEtale (pointHom K x)) : etale (p A P (RingPoints.map f x)) :=
    hp.etale_map P _ (by rw [pointHom_map]; exact hx.comp hfEtale)
  have hcover (y : localizedSpaceFunctor.obj Y') :
      ∃ (i : EtaleAffineTest K X') (z : localizedSpaceFunctor.obj _),
        localizedSpaceFunctor.map (g i) z = y := by
    obtain ⟨A, _, _, P, x, hx, hz⟩ := hp'.jointly_surjective y
    exact ⟨⟨CommAlgCat.of K A, P, x, hx⟩, hz⟩
  have hopen : IsOpen (range (localizedSpaceFunctor.map F)) :=
    isOpen_range_of_etale_composites F g hcover (fun i => by
      rw [show g i ≫ F = _ from hF i.algebra i.presentation i.point]
      exact hEtale i.algebra i.presentation i.point i.etale_point)
  let D := (presentationOf Y).openDomain (range (localizedSpaceFunctor.map F)) hopen
  let d := domainι Y D
  let G := domainLift D F (fun z => ⟨z, rfl⟩)
  have hG : G ≫ d = F := domainLift_comp D F _
  let q : PointFamily K X' (domainObj Y D) := fun A _ _ P x => p' A P x ≫ G
  have hqcomp (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A) :
      q A P x ≫ d = p A P (RingPoints.map f x) := by
    change (p' A P x ≫ G) ≫ d = _
    rw [Category.assoc, hG, hF]
  let : Mono (hom f) := SliceOpenGluing.relative_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone SliceOpenGluing.openProperty_le_monomorphisms _ hf)
  have hq : IsAnalytification K X' (domainObj Y D) q := by
    constructor
    · intro A B _ _ _ _ P Q φ x
      change (p' B Q (RingPoints.changeRing φ x)) ≫ G =
        AffineAnalytification.localizedHom K P Q φ ≫ p' A P x ≫ G
      rw [hp'.naturality P Q φ x, Category.assoc]
    · intro A _ _ P x hx
      apply etale_of_comp_domainι D
      change etale (q A P x ≫ d)
      rw [hqcomp]
      exact hEtale A P x hx
    · intro y
      obtain ⟨z, hz⟩ := y.property
      obtain ⟨A, _, _, P, x, hx, w, hw⟩ := hp'.jointly_surjective z
      refine ⟨A, inferInstance, inferInstance, P, x, hx, w, Subtype.ext ?_⟩
      have h := congrArg (fun m => localizedSpaceFunctor.map m w) (hqcomp A P x)
      rw [← hF] at h
      simpa only [Functor.map_comp, TopCat.comp_app, d, domainι_apply, hw, hz] using h
    · intro A B C _ _ _ _ _ _ P Q R a b x y h
      have hAlg : IsPullback
          ((schemeYoneda _).map (PointTopology.ringTestMap K a))
          ((schemeYoneda _).map (PointTopology.ringTestMap K b))
          (pointHom K (RingPoints.map f x)) (pointHom K (RingPoints.map f y)) := by
        rw [pointHom_map, pointHom_map]
        exact IsPullback.of_isLimit
          (PullbackCone.isLimitOfCompMono _ _ (hom f) _ h.isLimit)
      have hAn := hp.isPullback P Q R a b (RingPoints.map f x) (RingPoints.map f y) hAlg
      exact IsPullback.of_isLimit (PullbackCone.isLimitOfFactors _ _ d _ _
        (hqcomp _ P x) (hqcomp _ Q y) _ hAn.isLimit)
  obtain ⟨e, he⟩ := compatibleAnalytificationIso hp' hq hX' hX'ft G (fun _ _ _ _ _ => rfl)
  exact ⟨_, hopen, e, he ▸ hG⟩

end Langlands.Analytic.SpaceAnalytification
