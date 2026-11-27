import Langlands.Geometry.Analytic.SchemeAnalytificationLocalizedFunctor

/-! # The affine test models of localized scheme analytification -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Analytic.SchemeAnalytification

open _root_.CategoryTheory _root_.AlgebraicGeometry SaturatedAtlasPresentation
open AffineAnalytification AffineSchemeAnalytification
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Localized

private abbrev topChart (X : Scheme.{u}) [IsAffine X] : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩

private def topChartIso {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] : localized K (chartPresentation K f (topChart X)) ≅ object K f := by
  let D := chartDomain K f (topChart X)
  have h (y : localizedSpaceFunctor.obj (object K f)) :
      localizedSpaceFunctor.map (𝟙 (object K f)) y ∈ D.carrier := by
    change _ ∈ (chartDomain K f (topChart X)).carrier
    rw [chartDomain_carrier]
    exact trivial
  let inv := domainLift D (𝟙 (object K f)) h
  have w := domainLift_comp D (𝟙 (object K f)) h
  refine chartIso K f (topChart X) ≪≫ ⟨domainι (object K f) D, inv, ?_, w⟩
  apply (cancel_mono (domainι (object K f) D)).1
  rw [Category.assoc, w, Category.comp_id, Category.id_comp]

/-- A finite polynomial presentation gives a separated affine test scheme,
locally of finite type over the base field. -/
abbrev affineTestObject {A : Type u} [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) : (separatedLocallyFiniteTypeOver K).FullSubcategory := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  refine ⟨ringTest K A, ?_⟩
  change LocallyOfFiniteType (Spec.algebraMap K A) ∧ IsSeparated (Spec.algebraMap K A)
  refine ⟨?_, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
    (RingHom.finiteType_algebraMap.2 inferInstance)

private abbrev specTopRing (A : Type u) [CommRing A] [Algebra K A] :=
  CoordinateRing (structureMap (Spec.algebraMap K A) (topChart (Spec (CommRingCat.of A))))

private def specTopCoordinateEquiv (A : Type u) [CommRing A] [Algebra K A] :
    A ≃ₐ[K] specTopRing K A := by
  let f := Spec.algebraMap K A
  let Y := Spec (CommRingCat.of A)
  let j : ((⊤ : Y.Opens) : Scheme.{u}) ⟶ Y := Y.topIso.hom
  let e := Scheme.ΓSpecIso (CommRingCat.of A)
  let ψ : CommRingCat.of A ⟶ CommRingCat.of (specTopRing K A) := e.inv ≫ j.appTop
  let : IsIso j := Y.topIso.isIso_hom
  let : IsIso ψ := IsIso.comp_isIso
  refine AlgEquiv.ofBijective ⟨ψ.hom, fun c => ?_⟩ ((ConcreteCategory.isIso_iff_bijective ψ).mp inferInstance)
  let m := CommRingCat.ofHom (algebraMap K A)
  have h : m ≫ e.inv = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop :=
    Scheme.ΓSpecIso_inv_naturality m
  have w : m ≫ ψ =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (j ≫ f).appTop := by
    calc
      _ = (m ≫ e.inv) ≫ j.appTop := (Category.assoc _ _ _).symm
      _ = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop) ≫ j.appTop :=
        congrArg (· ≫ j.appTop) h
      _ = _ := by rw [Category.assoc, ← Scheme.Hom.comp_appTop]
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of (specTopRing K A) => g c) w

private def localizedIsoOfAlgEquiv {A B : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (e : A ≃ₐ[K] B) : localized K Q ≅ localized K P where
  hom := localizedHom K P Q e.toAlgHom
  inv := localizedHom K Q P e.symm.toAlgHom
  hom_inv_id := by
    have h := affineAnalytificationLocalizedFunctoriality K B A B Q Q P Q e.symm.toAlgHom e.toAlgHom
    rw [← h.2.2.2.1]
    rw [show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id K B from
      AlgHom.ext fun a => e.apply_symm_apply a, h.2.2.1]
  inv_hom_id := by
    have h := affineAnalytificationLocalizedFunctoriality K A B A P P Q P e.toAlgHom e.symm.toAlgHom
    rw [← h.2.2.2.1]
    rw [show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K A from
      AlgHom.ext fun a => e.symm_apply_apply a, h.2.2.1]

/-- On the spectrum of a test algebra with a finite polynomial presentation, localized scheme
analytification agrees with the specified polynomial-locus model. -/
def affineTestIso {A : Type u} [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) :
    localized K P ≅ (localizedAnalytification K).obj (affineTestObject K P) := by
  let f := Spec.algebraMap K A
  let : LocallyOfFiniteType f := (affineTestObject K P).property.1
  let V := topChart (Spec (CommRingCat.of A))
  exact localizedIsoOfAlgEquiv K (chartPresentation K f V) P (specTopCoordinateEquiv K A).symm ≪≫
    topChartIso K f

variable {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B) (φ : A →ₐ[K] B)

private theorem topChart_subordinate {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) : (topChart X : X.Opens) ≤ g ⁻¹ᵁ (topChart Y : Y.Opens) := by
  change ⊤ ≤ g ⁻¹ᵁ ⊤
  rw [Scheme.Hom.preimage_top]

private abbrev testCoordinateMap : specTopRing K A →ₐ[K] specTopRing K B :=
  openCoordinateMap (ringTestMap K φ).left (Over.w (ringTestMap K φ))
    (topChart_subordinate (ringTestMap K φ).left)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem testCoordinateMap_apply (a : A) :
    testCoordinateMap K φ (specTopCoordinateEquiv K A a) = specTopCoordinateEquiv K B (φ a) := by
  let m := CommRingCat.ofHom φ.toRingHom
  let g := (ringTestMap K φ).left
  let jA := (⊤ : (Spec (CommRingCat.of A)).Opens).ι
  let jB := (⊤ : (Spec (CommRingCat.of B)).Opens).ι
  let r := g.resLE _ _ (topChart_subordinate g)
  have hh : r ≫ jA = jB ≫ g := Scheme.Hom.resLE_comp_ι g (topChart_subordinate g)
  have ha : jA.appTop ≫ r.appTop = g.appTop ≫ jB.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hh]
  let eA := Scheme.ΓSpecIso (CommRingCat.of A)
  let eB := Scheme.ΓSpecIso (CommRingCat.of B)
  have hΓ : m ≫ eB.inv = eA.inv ≫ g.appTop := Scheme.ΓSpecIso_inv_naturality m
  have h : eA.inv ≫ jA.appTop ≫ r.appTop = m ≫ eB.inv ≫ jB.appTop := by
    rw [ha, ← Category.assoc eA.inv, ← hΓ, Category.assoc]
  exact congrArg (fun ψ : CommRingCat.of A ⟶ CommRingCat.of (specTopRing K B) => ψ a) h

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem compare_testPullback :
    φ.comp (specTopCoordinateEquiv K A).symm.toAlgHom =
      (specTopCoordinateEquiv K B).symm.toAlgHom.comp (testCoordinateMap K φ) := by
  apply AlgHom.ext
  intro a
  apply (specTopCoordinateEquiv K B).injective
  change specTopCoordinateEquiv K B (φ ((specTopCoordinateEquiv K A).symm a)) =
    specTopCoordinateEquiv K B ((specTopCoordinateEquiv K B).symm (testCoordinateMap K φ a))
  rw [AlgEquiv.apply_symm_apply, ← testCoordinateMap_apply, AlgEquiv.apply_symm_apply]

/-- The affine test comparison is natural for the map of spectra associated to a
homomorphism of the underlying test algebras. -/
theorem affineTestIso_naturality :
    localizedHom K P Q φ ≫ (affineTestIso K P).hom =
      (affineTestIso K Q).hom ≫ (localizedAnalytification K).map
        (ObjectProperty.homMk (ringTestMap K φ) : affineTestObject K Q ⟶ affineTestObject K P) := by
  let X := Spec (CommRingCat.of B)
  let Y := Spec (CommRingCat.of A)
  let f : X ⟶ Spec (CommRingCat.of K) := Spec.algebraMap K B
  let f' : Y ⟶ Spec (CommRingCat.of K) := Spec.algebraMap K A
  let : LocallyOfFiniteType f := (affineTestObject K Q).property.1
  let : LocallyOfFiniteType f' := (affineTestObject K P).property.1
  let R := chartPresentation K f' (topChart Y)
  let S := chartPresentation K f (topChart X)
  let g := (ringTestMap K φ).left
  let hg : g ≫ f' = f := Over.w (ringTestMap K φ)
  let i := topChart_subordinate g
  let eA := specTopCoordinateEquiv K A
  let eB := specTopCoordinateEquiv K B
  have hA := (affineAnalytificationLocalizedFunctoriality K _ _ _ R R P Q eA.symm.toAlgHom φ).2.2.2.1
  have hB := (affineAnalytificationLocalizedFunctoriality K _ _ _ R R S Q
    (testCoordinateMap K φ) eB.symm.toAlgHom).2.2.2.1
  change localizedHom K P Q φ ≫ (localizedHom K R P eA.symm.toAlgHom ≫ chartInclusion K f' (topChart Y)) =
    (localizedHom K S Q eB.symm.toAlgHom ≫ chartInclusion K f (topChart X)) ≫ map K f f' g hg
  rw [Category.assoc, chartInclusion_map K f f' g hg i, ← Category.assoc, ← Category.assoc, ← hA]
  change localizedHom K R Q (φ.comp eA.symm.toAlgHom) ≫ chartInclusion K f' (topChart Y) =
    (localizedHom K S Q eB.symm.toAlgHom ≫ localizedHom K R S (testCoordinateMap K φ)) ≫
      chartInclusion K f' (topChart Y)
  rw [← hB, compare_testPullback K φ]

end Localized

end Langlands.Analytic.SchemeAnalytification
