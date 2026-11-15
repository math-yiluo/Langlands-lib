import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPoints
import Langlands.Geometry.Analytic.EtaleSite
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-!
# Analytifications of algebraic spaces, tested on affine points

An analytification of an algebraic space `X` over `Spec K` is an analytic space `Y` in the
Library's localized category with a map `Spec(A)ᵃⁿ → Y` for every `A`-valued point of `X`.
These maps are natural in the test algebra `A`, étale for étale points, and jointly surjective
from étale points, and they carry fibre squares of affine test points to pullback squares.
-/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap AlgPoint)

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The morphism of presheaves `Spec A → X` attached to an `A`-valued point by the Yoneda
equivalence. -/
abbrev pointHom {X : AlgebraicSpace (Spec (CommRingCat.of K))} {A : Type u} [CommRing A]
    [Algebra K A] (x : RingPoints K X A) :
    (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ X.presheaf :=
  uliftYonedaEquiv.{u + 1}.symm x

/-- A family of morphisms in the localized category from the affine analytification of every
finitely presented test algebra, one for each test point of `X`. -/
abbrev PointFamily (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (Y : LocalizedCategory.{u, u, u} (K := K)) : Type (u + 1) :=
  ∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
    RingPoints K X A → (AffineAnalytification.localized K P ⟶ Y)

/-- `(Y, p)` is an analytification of the algebraic space `X`, tested on affine points:
1. `p` is natural in the test algebra: the map attached to the restriction of an `A`-point
   along `f : A →ₐ[K] B` is the analytified map `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` followed by the map
   attached to the point;
2. the map attached to an étale point is étale in the localized category;
3. the maps attached to étale points are jointly surjective on underlying points;
4. a fibre square of presheaves formed by affine test points and two algebra maps
   `f : A →ₐ[K] C`, `g : B →ₐ[K] C` is carried to a pullback square of analytic spaces. -/
structure IsAnalytification (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y) : Prop where
  naturality : ∀ {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (x : RingPoints K X A),
    p B Q (RingPoints.changeRing f x) = AffineAnalytification.localizedHom K P Q f ≫ p A P x
  etale_map : ∀ {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (x : RingPoints K X A), AlgebraicSpace.IsEtale (pointHom K x) →
      SaturatedAtlasPresentation.etale (p A P x)
  jointly_surjective : ∀ y : localizedSpaceFunctor.obj Y,
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (P : FinitePolynomialPresentation K A)
      (x : RingPoints K X A), AlgebraicSpace.IsEtale (pointHom K x) ∧
        y ∈ Set.range (localizedSpaceFunctor.map (p A P x))
  isPullback : ∀ {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra K C] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (R : FinitePolynomialPresentation K C)
    (f : A →ₐ[K] C) (g : B →ₐ[K] C) (x : RingPoints K X A) (y : RingPoints K X B),
    IsPullback ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f))
        ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g))
        (pointHom K x) (pointHom K y) →
      IsPullback (AffineAnalytification.localizedHom K P R f)
        (AffineAnalytification.localizedHom K Q R g) (p A P x) (p B Q y)

variable {K}

/-- The analytic point attached to a `K`-point `x` of `X`: the image under the map attached
to `x` of the analytic point of the identity of `K`, for a presentation `P₀` of `K`. -/
def rationalPoint {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y : LocalizedCategory.{u, u, u} (K := K)} (p : PointFamily K X Y)
    (P₀ : FinitePolynomialPresentation K K) (x : RingPoints K X K) :
    localizedSpaceFunctor.obj Y :=
  localizedSpaceFunctor.map (p K P₀ x)
    (AffineAnalytification.analyticPoint K P₀ (AlgPoint.ofAlgHom (AlgHom.id K K)))

/-- Composing an analytification with an isomorphism of analytic spaces gives an
analytification. -/
theorem IsAnalytification.comp_iso {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y Y' : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p) (e : Y ≅ Y') :
    IsAnalytification K X Y' (fun A _ _ P x => p A P x ≫ e.hom) where
  naturality P Q f x := by
    rw [hp.naturality P Q f x, Category.assoc]
  etale_map P x hx :=
    MorphismProperty.RespectsIso.postcomp (SaturatedAtlasPresentation.etale (K := K)) e.hom _
      (hp.etale_map P x hx)
  jointly_surjective y := by
    obtain ⟨A, _, _, P, x, hx, z, hz⟩ :=
      hp.jointly_surjective (localizedSpaceFunctor.map e.inv y)
    refine ⟨A, inferInstance, inferInstance, P, x, hx, z, ?_⟩
    rw [CategoryTheory.Functor.map_comp, TopCat.comp_app, hz, ← TopCat.comp_app,
      ← CategoryTheory.Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      TopCat.id_app]
  isPullback P Q R f g x y h :=
    (hp.isPullback P Q R f g x y h).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp) (by simp)

/-- The analytic point of a `K`-point after composing with an isomorphism. -/
theorem rationalPoint_comp_iso {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y Y' : LocalizedCategory.{u, u, u} (K := K)} (p : PointFamily K X Y) (e : Y ≅ Y')
    (P₀ : FinitePolynomialPresentation K K) (x : RingPoints K X K) :
    rationalPoint (fun A _ _ P x => p A P x ≫ e.hom) P₀ x =
      localizedSpaceFunctor.map e.hom (rationalPoint p P₀ x) := by
  simp only [rationalPoint, CategoryTheory.Functor.map_comp]
  rfl

end Langlands.Analytic.SpaceAnalytification
