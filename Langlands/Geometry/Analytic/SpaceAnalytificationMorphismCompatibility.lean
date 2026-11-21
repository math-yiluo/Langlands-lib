import Langlands.Geometry.Analytic.SpaceAnalytificationAffineIntersections

/-! # Agreement of image maps on overlaps of affine test points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Let `X'` be separated, `f : X' ⟶ X`, and let `(Y', p')`, `(Y, p)` be analytifications
of `X'` and `X`. If two maps `g₁`, `g₂` into affine analytifications become equal after
composition with the maps `p'` of test points `x`, `y` of `X'`, then they also become equal
after composition with the maps `p` of the image points `f x`, `f y`. -/
theorem IsAnalytification.comp_map_eq_of_comp_eq
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX' : IsSeparated X')
    (f : X' ⟶ X) {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    {S : LocalizedCategory.{u, u, u} (K := K)}
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X' A) (y : RingPoints K X' B)
    (g₁ : S ⟶ AffineAnalytification.localized K P)
    (g₂ : S ⟶ AffineAnalytification.localized K Q)
    (h : g₁ ≫ p' A P x = g₂ ≫ p' B Q y) :
    g₁ ≫ p A P (RingPoints.map f x) = g₂ ≫ p B Q (RingPoints.map f y) := by
  obtain ⟨C, _, _, R, a, b, hC⟩ := exists_affine_test_intersection hX' P Q x y
  obtain ⟨c, hc₁, hc₂⟩ := (hp'.isPullback P Q R a b x y hC).exists_lift g₁ g₂ h
  have hxy : RingPoints.changeRing a x = RingPoints.changeRing b y := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    have ha : pointHom K (RingPoints.changeRing a x) =
        (schemeYoneda _).map (ringTestMap K a) ≫ pointHom K x :=
      uliftYonedaEquiv_symm_map (ringTestMap K a).op x
    have hb : pointHom K (RingPoints.changeRing b y) =
        (schemeYoneda _).map (ringTestMap K b) ≫ pointHom K y :=
      uliftYonedaEquiv_symm_map (ringTestMap K b).op y
    exact ha.trans (hC.w.trans hb.symm)
  have hfxy : RingPoints.changeRing a (RingPoints.map f x) =
      RingPoints.changeRing b (RingPoints.map f y) := by
    rw [RingPoints.changeRing_map, RingPoints.changeRing_map, hxy]
  rw [← hc₁, ← hc₂, Category.assoc, Category.assoc, ← hp.naturality P R a,
    ← hp.naturality Q R b, hfxy]

end Langlands.Analytic.SpaceAnalytification
