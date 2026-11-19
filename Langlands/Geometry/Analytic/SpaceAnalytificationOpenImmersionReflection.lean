import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.SpaceAnalytificationMonomorphismReflection
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages

/-! # Reflection of open immersions by analytification -/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
  {G : Presheaf S} (a : G ⟶ X'.presheaf)

set_option backward.isDefEq.respectTransparency false in
private theorem sheafify_range_comp_eq_of_mono [Mono (hom f)]
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a) :
    (Subfunctor.range (a ≫ hom f)).sheafify (fppfTopology S) = Subfunctor.range (hom f) := by
  have hRange : CategoryTheory.Presheaf.IsSheaf (fppfTopology S)
      (Subfunctor.range (hom f)).toFunctor :=
    (CategoryTheory.Presheaf.isSheaf_of_iso_iff (asIso (Subfunctor.toRange (hom f)))).mp
      X'.toSheaf.property
  apply le_antisymm
  · apply Subfunctor.sheafify_le _ _ ?_
      ((isSheaf_iff_isSheaf_of_type _ _).mp X.toSheaf.property)
      ((isSheaf_iff_isSheaf_of_type _ _).mp hRange)
    rintro T _ ⟨z, rfl⟩
    exact ⟨a.app T z, rfl⟩
  · rintro T _ ⟨x, rfl⟩
    change _ ∈ fppfTopology S T.unop
    apply (fppfTopology S).superset_covering _ (ha.imageSieve_mem x)
    intro W r hr
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, ?_⟩
    change (hom f).app (op W) (a.app (op W) z) =
      X.presheaf.map r.op ((hom f).app T x)
    rw [hz, (hom f).naturality_apply]

/-- The sheafified image of a locally surjective presentation followed by a
monomorphism is canonically isomorphic to the source of the monomorphism. -/
def sheafifiedImageIsoOfMono [Mono (hom f)]
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a) :
    { e : X'.presheaf ≅ ((Subfunctor.range (a ≫ hom f)).sheafify (fppfTopology S)).toFunctor //
      e.hom ≫ ((Subfunctor.range (a ≫ hom f)).sheafify (fppfTopology S)).ι = hom f } := by
  rw [sheafify_range_comp_eq_of_mono f a ha]
  exact ⟨asIso (Subfunctor.toRange (hom f)), Subfunctor.toRange_ι _⟩

/-- An étale monomorphism of algebraic spaces is a representable open immersion. -/
theorem isOpenImmersion_of_isEtaleMorphism_of_mono [Mono (hom f)]
    (hf : IsEtaleMorphism f) : IsOpenImmersion (hom f) := by
  obtain ⟨U, a, _, ha, hs⟩ := X'.exists_atlas
  obtain ⟨e, he⟩ := sheafifiedImageIsoOfMono f a
    (isLocallySurjective_of_isEtale_isSurjective a ha hs)
  have h := OpenSubfunctorImages.sheafify_range_open (a ≫ hom f) (hf U a ha)
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp
    ((SliceOpenGluing.openProperty S).relative (schemeYoneda S)) e.hom _ h

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An analytic open immersion reflects to an algebraic open immersion,
assuming localized étale pullbacks and reflection of étaleness on affines. -/
theorem isOpenImmersion_of_openImmersion_of_affineReflection
    (hPullback : LocalizedEtalePullbackStatement.{u, u} K)
    (hAffineReflect : ∀ (A B : Type u) [CommRing A] [Algebra K A]
      [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (g : A →ₐ[K] B), etale (AffineAnalytification.localizedHom K P Q g) →
        g.toRingHom.Etale)
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX'sep : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
    (hXsep : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)} {p' : PointFamily K X' Y'}
    {p : PointFamily K X Y} (hp' : IsAnalytification K X' Y' p')
    (hp : IsAnalytification K X Y p) {F : Y' ⟶ Y}
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
        p' A P x ≫ F = p A P (RingPoints.map f x))
    (ho : openImmersion F) : AlgebraicSpace.IsOpenImmersion (hom f) := by
  have hEtale : etale F := by
    obtain ⟨U, hU, e, rfl⟩ := ho
    exact etale_comp (etale_of_isIso e.hom) (etaleOpenDomainStatement Y U hU)
  let : Mono F := by
    obtain ⟨U, hU, e, rfl⟩ := ho
    infer_instance
  let : Mono (hom f) :=
    mono_of_mono_analytification f hp' hp hF hAffineReflect hX'sep hXsep hX'ft
  apply isOpenImmersion_of_isEtaleMorphism_of_mono f
  apply (isEtaleMorphism_iff_finiteTypeAffineTests f hX'ft).mpr
  intro A _ _ _ x hx
  let P := FinitePolynomialPresentation.ofFiniteType K A
  have h : etale (p A P (RingPoints.map f x)) := by
    rw [← hF A P x]
    exact etale_comp (hp'.etale_map P x hx) hEtale
  simpa only [pointHom_map] using
    isEtale_pointHom_of_etale_of_affineReflection K hPullback hAffineReflect
      hXsep hXft hp P (RingPoints.map f x) h

end Langlands.Analytic.SpaceAnalytification
