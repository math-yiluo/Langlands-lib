/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback


public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverCoefficient
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHom
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOverMapCoefficient

/-! # Raw cohomology pullback and the higher-image comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

/-- Raw cohomology with coefficients restricted from W. -/
noncomputable abbrev higherDirectImageRawOverPresheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :=
  higherDirectImagePresheaf Λ (B.hom ≫ k) q
    (higherDirectImageRawOverComplex Λ G B)

/-- The canonical raw comparison, with its underlying abelian target made explicit. -/
noncomputable abbrev higherDirectImageRawOverComparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :
    higherDirectImageRawOverPresheaf Λ k G q B ⟶
      (higherDirectImage Λ (B.hom ≫ k) q
        (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
  higherDirectImagePresheafToSheaf Λ (B.hom ≫ k) q
    (higherDirectImageRawOverComplex Λ G B)

/-- Pullback of a raw cohomology class for coefficients restricted from W.
The factors are pullback composition, the single-functor comparison, pullback
of the class, shift comparison, and the canonical coefficient identification.
Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps. -/
@[implicit_reducible]
noncomputable def higherDirectImageRawOverPullback
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  higherDirectImageRawTrianglePullback Λ f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) q _ _
    (higherDirectImageRawOverCoefficient Λ G f) U z

attribute [local irreducible] lowerStarPlusTransition higherDirectImagePresheafToHom

private theorem evaluation_postcomp
    (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}} (U : S.Etale)
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (β : (freeSheaf Λ S).obj U ⟶ F) (m : F ⟶ G) :
    (freeSheafSections Λ G).app (op U) (β ≫ m) =
      m.hom.app (op U) ((freeSheafSections Λ F).app (op U) β) := by
  have h := freeSheafSections_naturality (Λ := Λ) m
  exact (congrArg (fun n ↦ n.app (op U) β) h).symm

/-- The comparison component of raw pullback with the higher direct image map.
Source: Stacks Project, Tags 03Q8 and 09Z1; canonical derived-Hom comparison.
(blueprint: sbc-lem-higher-image-raw-over-comparison).
The proof expands the adjunction comparison, applies the triangle identity,
and identifies the resulting shifted homology map with the canonical transition.
-/
theorem higherDirectImageRawOverPullback_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverComparison Λ k G q A).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z) =
    ((higherDirectImageOverMap Λ k G q f).hom.app (op U))
      ((higherDirectImageRawOverComparison Λ k G q B).app (op U) z) := by
  rw [← higherDirectImageOverMap_coefficient Λ k G q f]
  change (freeSheafSections Λ _).app (op U)
      ((higherDirectImagePresheafToHom Λ (A.hom ≫ k) q _).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z)) = _
  exact (congrArg ((freeSheafSections Λ _).app (op U))
    (higherDirectImageRawTransition_toHom Λ f.left
      (B.hom ≫ k) (A.hom ≫ k) (by rw [← Category.assoc, Over.w]) q _ _
      (higherDirectImageRawOverCoefficient Λ G f) U z)).trans
    (evaluation_postcomp Λ U _ _)

/-- Restriction component of raw pullback naturality.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-restriction).
The proof is the naturality of the pullback composition and single-complex
comparison maps under restriction of the étale test object.
-/
theorem higherDirectImageRawOverPullback_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U))
    (T : S.Etale) (a : T ⟶ U) :
      higherDirectImageRawOverPullback Λ k G q f T
        ((higherDirectImageRawOverPresheaf Λ k G q B).map a.op z) =
      (higherDirectImageRawOverPresheaf Λ k G q A).map a.op
            (higherDirectImageRawOverPullback Λ k G q f U z) := by
  unfold higherDirectImageRawOverPullback
  apply higherDirectImageRawTrianglePullback_restriction

/-- Raw pullback intertwines the fixed cohomology-presheaf comparison with the
canonical higher-image transition. This requires no limit or qcqs assumptions.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).

Proof: Expand the raw class comparison as derived adjunction followed by degree-zero
homology and evaluation at the identity generator of the free module sheaf of U.
Expand the transition as unit, pullback composition, and counit. Naturality of the
unit moves the class through pullback, and the triangle identity cancels the
counit against the unit in its adjoint image. The pullback composition comparison
on single complexes then gives the first two factors of the raw pullback. Shift
compatibility gives its fourth factor; the last factor is the shifted coefficient
identification. Naturality of homology and evaluation proves the equality.
For restriction along a : T -> U, use naturality of the pullback composition
and single-functor isomorphisms in the free sheaf of U. Functoriality moves its
precomposition through pullback; associativity gives the second equality.
The comparisons are the fixed constructions, not arbitrarily chosen isomorphisms. -/
theorem higherDirectImageRawOverPullback_toSheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverComparison Λ k G q A).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z) =
    ((higherDirectImageOverMap Λ k G q f).hom.app (op U))
      ((higherDirectImageRawOverComparison Λ k G q B).app (op U) z) ∧
    ∀ (T : S.Etale) (a : T ⟶ U),
      higherDirectImageRawOverPullback Λ k G q f T
        ((higherDirectImageRawOverPresheaf Λ k G q B).map a.op z) =
      (higherDirectImageRawOverPresheaf Λ k G q A).map a.op
            (higherDirectImageRawOverPullback Λ k G q f U z)  := by
  exact ⟨higherDirectImageRawOverPullback_comparison Λ k G q f U z,
    fun T a => higherDirectImageRawOverPullback_restriction Λ k G q f U z T a⟩

end AlgebraicGeometry.Etale
