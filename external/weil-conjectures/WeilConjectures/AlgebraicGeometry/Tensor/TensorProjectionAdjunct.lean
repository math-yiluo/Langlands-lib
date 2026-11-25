/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensorSymmetryInvolutive

/-!
# Adjoint of a tensor-projected morphism

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-lem-geo-p1-cohomology/thm-amb-p1-decomposition.proof.md`
(blueprint: lem-amb-tensor-projection-adjunct).

The proof expands the projection-map mate, uses compatibility of the canonical
inverse-image tensor comparison with the signed symmetry, cancels the two opposite
symmetries, and applies naturality and bifunctoriality of the derived tensor product.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem projection_adjunct_calculation
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D)
    (sP : P ⟶ P.flip) (sQ : Q ⟶ Q.flip)
    (c : ∀ U V, F.obj ((P.obj U).obj V) ⟶ (Q.obj (F.obj U)).obj (F.obj V))
    (hc : ∀ U V, F.map ((sP.app U).app V) ≫ c V U =
      c U V ≫ (sQ.app (F.obj U)).app (F.obj V))
    (hn : ∀ U {V V'} (a : V ⟶ V'), F.map ((P.obj U).map a) ≫ c U V' =
      c U V ≫ (Q.obj (F.obj U)).map (F.map a))
    (hs : ∀ U V, (sQ.app U).app V ≫ (sQ.app V).app U = 𝟙 _)
    (K M : C) (E : D) (a : M ⟶ G.obj E)
    (p : (P.obj (G.obj E)).obj K ⟶ G.obj ((Q.obj E).obj (F.obj K)))
    (hp : (adj.homEquiv _ _).symm p =
      c (G.obj E) K ≫ (Q.map (adj.counit.app E)).app (F.obj K)) :
    (adj.homEquiv _ _).symm
      ((P.obj K).map a ≫ (sP.app K).app (G.obj E) ≫ p ≫
        G.map ((sQ.app E).app (F.obj K))) =
      c K M ≫ (Q.obj (F.obj K)).map (F.map a ≫ adj.counit.app E) := by
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  erw [hp]
  simp only [Category.assoc]
  rw [reassoc_of% (hc K (G.obj E))]
  have hnat := NatTrans.congr_app (sQ.naturality (adj.counit.app E)) (F.obj K)
  change (Q.map (adj.counit.app E)).app (F.obj K) ≫
      (sQ.app E).app (F.obj K) =
    (sQ.app (F.obj (G.obj E))).app (F.obj K) ≫
      (Q.obj (F.obj K)).map (adj.counit.app E) at hnat
  rw [hnat, reassoc_of% (hs (F.obj K) (F.obj (G.obj E))),
    ← Category.assoc, hn, Category.assoc, ← (Q.obj _).map_comp]

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem tensor_projection_adjunct_general
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hc : ∀ U V : DerivedCategory (Sheaf Y.smallEtaleTopology A),
      (L((f)^*[A])).map (((derivedTensorSymmetry A Y).hom.app U).app V) ≫
          ((leftDerivedUpperStarTensorComparison A f).app V).app U =
        ((leftDerivedUpperStarTensorComparison A f).app U).app V ≫
          ((derivedTensorSymmetry A X).hom.app ((L((f)^*[A])).obj U)).app
            ((L((f)^*[A])).obj V))
    (hs : ∀ U V : DerivedCategory (Sheaf X.smallEtaleTopology A),
      ((derivedTensorSymmetry A X).hom.app U).app V ≫
        ((derivedTensorSymmetry A X).hom.app V).app U = 𝟙 _)
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (a : M ⟶ (R((f)_*[A])).obj E) :
    ((derivedUpperStarLowerStarAdjunction A f).homEquiv
        (((derivedTensor A Y).obj K).obj M)
        (((derivedTensor A X).obj
          ((L((f)^*[A])).obj K)).obj E)).symm
      (((derivedTensor A Y).obj K).map a ≫
        ((derivedTensorSymmetry A Y).hom.app K).app
          ((R((f)_*[A])).obj E) ≫
        ((rightDerivedLowerStarProjectionMap A f).app E).app K ≫
        (R((f)_*[A])).map
          (((derivedTensorSymmetry A X).hom.app E).app
            ((L((f)^*[A])).obj K))) =
      ((leftDerivedUpperStarTensorComparison A f).app K).app M ≫
        ((derivedTensor A X).obj
          ((L((f)^*[A])).obj K)).map
          ((L((f)^*[A])).map a ≫
            (derivedUpperStarLowerStarAdjunction A f).counit.app E) := by
  exact projection_adjunct_calculation
    (derivedUpperStarLowerStarAdjunction A f)
    (derivedTensor A Y) (derivedTensor A X)
    (derivedTensorSymmetry A Y).hom (derivedTensorSymmetry A X).hom
    (fun U V ↦ ((leftDerivedUpperStarTensorComparison A f).app U).app V)
    hc
    (fun U _ _ a ↦ leftDerivedUpperStarTensorIso_hom_naturality_right (A := A) f U a)
    hs K M E a _ (homEquiv_symm_rightDerivedLowerStarProjectionMap A f E K)

attribute [local instance high] SymmetricCategory.toBraidedCategory in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/--
Source: the final tensor/projection-formula sentence of
`thm-amb-p1-decomposition.proof.md` (blueprint: lem-amb-tensor-projection-adjunct).

For an arbitrary scheme morphism and commutative coefficient ring, the adjoint of the
symmetrized projection map after tensoring with `a` is tensoring the adjoint of `a` with the
fixed inverse-image factor.  The proof expands the mate of the canonical projection map,
uses the natural inverse-image tensor comparison and the signed tensor symmetry, and then
uses the derived tensor bifunctor law.  No properness, boundedness, finiteness, torsion or
invertibility hypothesis is used.
-/
theorem tensorProjectionAdjunct
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategoryModule Λ Y) (E : DerivedCategoryModule Λ X)
    (a : M ⟶ (R((f)_*[ModuleCat.{u + 1} Λ])).obj E) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj M)
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj E)).symm
      (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).map a ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app K).app
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K ≫
        (R((f)_*[ModuleCat.{u + 1} Λ])).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app E).app
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))) =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) f).app K).app M ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).map
          ((L((f)^*[ModuleCat.{u + 1} Λ])).map a ≫
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app E) := by
  exact tensor_projection_adjunct_general (ModuleCat.{u + 1} Λ) f
    (derivedPullback_tensorSymmetry Λ f) (derivedTensorSymmetry_involutive Λ X) K M E a

end AlgebraicGeometry.Etale
