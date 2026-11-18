import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleStatement
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAffineTests
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Conditional reductions for étaleness of algebraic-space analytifications -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Evaluation on ring points agrees with composition of the represented point. -/
theorem pointHom_map {X' X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (f : X' ⟶ X) {A : Type u} [CommRing A] [Algebra K A] (x : RingPoints K X' A) :
    pointHom K (RingPoints.map f x) = pointHom K x ≫ hom f :=
  (uliftYonedaEquiv_symm_comp x (hom f)).symm

/-- The actual étale affine test points, with their algebra structures and
presentations retained. Its index universe is `u + 1`. -/
structure EtaleAffineTest (X : AlgebraicSpace (Spec (CommRingCat.of K))) where
  algebra : CommAlgCat.{u} K
  presentation : FinitePolynomialPresentation K algebra
  point : RingPoints K X algebra
  etale_point : AlgebraicSpace.IsEtale (pointHom K point)

/-- Source descent is the only additional input needed for preservation of
étaleness by a compatible map of analytifications. -/
theorem etale_of_isEtaleMorphism_of_sourceDescent
    (hSource : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : LocalizedCategory.{u, u, u} (K := K)) (F : X ⟶ Y)
      (ι : Type (u + 1)) (U : ι → LocalizedCategory.{u, u, u} (K := K))
      (q : ∀ i, U i ⟶ X),
      (∀ i, etale (q i)) →
      (∀ x : localizedSpaceFunctor.obj X,
        ∃ i, x ∈ Set.range (localizedSpaceFunctor.map (q i))) →
      (∀ i, etale (q i ≫ F)) → etale F)
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    (hf : IsEtaleMorphism f) : etale F := by
  refine hSource K Y' Y F (EtaleAffineTest K X')
    (fun t => AffineAnalytification.localized K t.presentation)
    (fun t => p' t.algebra t.presentation t.point) ?_ ?_ ?_
  · intro t
    exact hp'.etale_map t.presentation t.point t.etale_point
  · intro y
    obtain ⟨A, _, _, P, x, hx, hy⟩ := hp'.jointly_surjective y
    exact ⟨⟨CommAlgCat.of K A, P, x, hx⟩, hy⟩
  · intro t
    rw [hF]
    apply hp.etale_map
    rw [pointHom_map]
    exact hf _ _ t.etale_point

/-- Reflection on affine test points, together with source descent, closes the
comparison. Both missing analytic inputs are explicit hypotheses. -/
theorem isEtaleMorphism_iff_etale_of_sourceDescent_of_pointReflection
    (hSource : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : LocalizedCategory.{u, u, u} (K := K)) (F : X ⟶ Y)
      (ι : Type (u + 1)) (U : ι → LocalizedCategory.{u, u, u} (K := K))
      (q : ∀ i, U i ⟶ X),
      (∀ i, etale (q i)) →
      (∀ x : localizedSpaceFunctor.obj X,
        ∃ i, x ∈ Set.range (localizedSpaceFunctor.map (q i))) →
      (∀ i, etale (q i ≫ F)) → etale F)
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX' : LocallyOfFiniteTypeOverBase X')
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (hReflect : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X A),
      etale (p A P x) → AlgebraicSpace.IsEtale (pointHom K x))
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x)) :
    IsEtaleMorphism f ↔ etale F := by
  constructor
  · exact etale_of_isEtaleMorphism_of_sourceDescent K hSource f hp' hp F hF
  · intro hEtale
    apply (isEtaleMorphism_iff_finiteTypeAffineTests f hX').mpr
    intro A _ _ _ x hx
    let P := FinitePolynomialPresentation.ofFiniteType K A
    have hComp := etale_comp (hp'.etale_map P x hx) hEtale
    rw [hF] at hComp
    have hPoint := hReflect A P (RingPoints.map f x) hComp
    simpa only [pointHom_map] using hPoint

end Langlands.Analytic.SpaceAnalytification
