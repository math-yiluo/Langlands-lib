import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability
import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidNaturality
import Langlands.Geometry.Analytic.SpaceAnalytificationAffineIntersections
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidPoints
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReduction

/-! # Affinoid tests for algebraic-space analytifications -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open AffineAnalytification SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

/-- The small affinoid spectrum as a localized analytic space. -/
abbrev localizedAffinoidSpectrum (R : PresentedAffinoidAlgebra K) :
    LocalizedCategory.{u, u, u} (K := K) :=
  localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, u} R)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem ringTestMap_injective {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] :
    Function.Injective (ringTestMap K (A := A) (B := B)) := by
  intro f g h
  apply AlgHom.coe_ringHom_injective
  exact congrArg (fun q => q.hom) (Spec.map_injective (congrArg (fun q => q.left) h))

set_option backward.isDefEq.respectTransparency false in
/-- Two affine factorizations agree analytically precisely when they give the same ring
point. The coefficient algebra of the test may be any presented affinoid algebra. -/
theorem localized_affinoid_test_eq_iff (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (R : PresentedAffinoidAlgebra K)
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X A) (y : RingPoints K X B) (φ : A →ₐ[K] R) (ψ : B →ₐ[K] R) :
    localizedAffinoidHom K P R φ ≫ p A P x = localizedAffinoidHom K Q R ψ ≫ p B Q y ↔
      RingPoints.changeRing φ x = RingPoints.changeRing ψ y := by
  obtain ⟨C, _, _, T, f, g, hAlg⟩ := exists_affine_test_intersection hX P Q x y
  have hAn := hp.isPullback P Q T f g x y hAlg
  constructor
  · intro h
    let l := hAn.lift _ _ h
    obtain ⟨δ, hδ⟩ := (localizedAffinoidHomEquiv K T R).surjective l
    rw [localizedAffinoidHomEquiv_apply] at hδ
    have hf : δ.comp f = φ := (localizedAffinoidHomEquiv K P R).injective (by
      rw [localizedAffinoidHomEquiv_apply, localizedAffinoidHomEquiv_apply,
        ← localizedAffinoidHom_comp K P R T f δ, hδ]
      exact hAn.lift_fst _ _ h)
    have hg : δ.comp g = ψ := (localizedAffinoidHomEquiv K Q R).injective (by
      rw [localizedAffinoidHomEquiv_apply, localizedAffinoidHomEquiv_apply,
        ← localizedAffinoidHom_comp K Q R T g δ, hδ]
      exact hAn.lift_snd _ _ h)
    apply (uliftYonedaEquiv.{u + 1}).symm.injective
    change pointHom K _ = pointHom K _
    rw [← hf, ← hg, pointHom_changeRing, pointHom_changeRing,
      ringTestMap_comp, ringTestMap_comp, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, hAlg.w]
  · intro h
    have heq : (schemeYoneda _).map (ringTestMap K φ) ≫ pointHom K x =
        (schemeYoneda _).map (ringTestMap K ψ) ≫ pointHom K y := by
      rw [← pointHom_changeRing, ← pointHom_changeRing, h]
    let l := hAlg.lift _ _ heq
    obtain ⟨m, hm⟩ := (schemeYoneda _).map_surjective l
    let δ := affineRingPointEquiv K C R m
    have hδ : (schemeYoneda _).map (ringTestMap K δ) = l :=
      (congrArg ((schemeYoneda _).map) (ringTestMap_affineRingPointEquiv K m)).trans hm
    have hf : δ.comp f = φ := ringTestMap_injective (K := K)
      ((schemeYoneda _).map_injective (by
        rw [ringTestMap_comp, Functor.map_comp, hδ]
        exact hAlg.lift_fst _ _ heq))
    have hg : δ.comp g = ψ := ringTestMap_injective (K := K)
      ((schemeYoneda _).map_injective (by
        rw [ringTestMap_comp, Functor.map_comp, hδ]
        exact hAlg.lift_snd _ _ heq))
    rw [← hf, ← hg, ← localizedAffinoidHom_comp K P R T f δ,
      ← localizedAffinoidHom_comp K Q R T g δ, Category.assoc, Category.assoc, hAn.w]

private theorem exists_affinoid_point_hom (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    (R : PresentedAffinoidAlgebra K) (x : RingPoints K X R) :
    ∃ m : localizedAffinoidSpectrum R ⟶ Y,
      ∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
        (φ : A →ₐ[K] R) (y : RingPoints K X A),
        RingPoints.changeRing φ y = x → m = localizedAffinoidHom K P R φ ≫ p A P y := by
  obtain ⟨B, _, _, Q, ψ, z, hz⟩ := exists_polynomial_point_factorization hft x
  refine ⟨localizedAffinoidHom K Q R ψ ≫ p B Q z, ?_⟩
  intro A _ _ P φ y hy
  exact (localized_affinoid_test_eq_iff hp hX R Q P z y ψ φ).2 (hz.trans hy.symm)

/-- The map attached to an affinoid-algebra point of a separated locally
finite type space, obtained from any finite polynomial test for the point. -/
def affinoidPointHom (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    (R : PresentedAffinoidAlgebra K) (x : RingPoints K X R) :
    localizedAffinoidSpectrum R ⟶ Y :=
  (exists_affinoid_point_hom hp hX hft R x).choose

theorem affinoidPointHom_test (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    (R : PresentedAffinoidAlgebra K)
    {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (φ : A →ₐ[K] R) (y : RingPoints K X A) :
    affinoidPointHom hp hX hft R (RingPoints.changeRing φ y) =
      localizedAffinoidHom K P R φ ≫ p A P y :=
  (exists_affinoid_point_hom hp hX hft R (RingPoints.changeRing φ y)).choose_spec A P φ y rfl

theorem affinoidPointHom_injective (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    (R : PresentedAffinoidAlgebra K) :
    Function.Injective (affinoidPointHom hp hX hft R) := by
  intro x y h
  obtain ⟨A, _, _, P, φ, x', rfl⟩ := exists_polynomial_point_factorization hft x
  obtain ⟨B, _, _, Q, ψ, y', rfl⟩ := exists_polynomial_point_factorization hft y
  rw [affinoidPointHom_test, affinoidPointHom_test] at h
  exact (localized_affinoid_test_eq_iff hp hX R P Q x' y' φ ψ).1 h

/-- Changing coefficients by a bounded map is precomposition by the
associated morphism of localized affinoid spectra. -/
theorem affinoidPointHom_changeRing (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    {R S : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K R S) (x : RingPoints K X R) :
    affinoidPointHom hp hX hft S (RingPoints.changeRing g.toAlgHom x) =
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g) ≫
        affinoidPointHom hp hX hft R x := by
  obtain ⟨A, _, _, P, φ, y, rfl⟩ := exists_polynomial_point_factorization hft x
  rw [← SpaceFilteredRingPoints.changeRing_comp φ g.toAlgHom y, affinoidPointHom_test hp hX hft S P,
    affinoidPointHom_test hp hX hft R P, ← Category.assoc, localizedAffinoidHom_precomp]

/-- A map compatible with affine polynomial tests is also compatible with
the induced affinoid tests. -/
theorem affinoidPointHom_comp (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    {X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y' : LocalizedCategory.{u, u, u} (K := K)} {q : PointFamily K X' Y'}
    (hq : IsAnalytification K X' Y' q) (hX' : IsSeparated X')
    (hft' : LocallyOfFiniteTypeOverBase X') (f : X ⟶ X') (F : Y ⟶ Y')
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X A),
      p A P x ≫ F = q A P (RingPoints.map f x))
    (R : PresentedAffinoidAlgebra K) (x : RingPoints K X R) :
    affinoidPointHom hp hX hft R x ≫ F =
      affinoidPointHom hq hX' hft' R (RingPoints.map f x) := by
  obtain ⟨A, _, _, P, φ, y, rfl⟩ := exists_polynomial_point_factorization hft x
  rw [← RingPoints.changeRing_map, affinoidPointHom_test hp hX hft R P,
    affinoidPointHom_test hq hX' hft' R P, Category.assoc, hF]

end Langlands.Analytic.SpaceAnalytification
