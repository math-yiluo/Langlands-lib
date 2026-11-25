/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Scalar faithfulness after the ordinary inverse-image adjunction

Source: the two components of blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace Scheme.finiteEtaleTateLine
  ordinaryFiniteP1ChernSpec ordinaryFiniteP1ChernPushforward
set_option allowUnsafeReducibility true in
attribute [local reducible] ordinaryFiniteDegreeZero ordinaryFiniteLine ordinaryFiniteUnit

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedUpperStarLowerStarAdjunction HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors

local instance (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePushforward A f).PreservesZeroMorphisms := by
  let : (ordinaryFinitePushforward A f).Additive :=
    additive_rightDerivedLowerStar (ModuleCat.{u + 1} A) f
  infer_instance

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_adj_precomp_zero
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (L : C ⥤ D) (G : D ⥤ C) [G.PreservesZeroMorphisms] (adj : L ⊣ G)
    {V : C} {X Y : D} (v : L.obj V ≅ X) (φ : V ⟶ V) (ψ : X ⟶ X)
    (hv : L.map φ ≫ v.hom = v.hom ≫ ψ) (c : X ⟶ Y)
    (ha : φ ≫ adj.homEquiv _ _ (v.hom ≫ c) = 0) : ψ ≫ c = 0 := by
  apply (cancel_epi v.hom).mp
  apply (adj.homEquiv _ _).injective
  rw [← Category.assoc, ← hv, Category.assoc, Adjunction.homEquiv_naturality_left]
  simpa only [comp_zero, Adjunction.homEquiv_unit, Functor.map_zero] using ha

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_linear_scalar_naturality
    (R : Type*) [CommRing R]
    {B B' C D : Type*} [Category B] [Category B'] [Category C] [Category D]
    [Preadditive B] [Preadditive B'] [Preadditive C] [Preadditive D]
    [Linear R B] [Linear R B'] [Linear R C] [Linear R D]
    (S : B ⥤ C) (L : C ⥤ D) (T : B' ⥤ D)
    [S.Linear R] [L.Linear R] [T.Linear R]
    (X : B) (Y : B') (e : L.obj (S.obj X) ⟶ T.obj Y) (a : R) :
    L.map (S.map (a • 𝟙 X)) ≫ e = e ≫ T.map (a • 𝟙 Y) := by
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id]

private theorem kummer_unit_scalar_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
     {X Y : Scheme.{u}} (f : X ⟶ Y) (a : A) :
    (ordinaryFinitePullback A f).map
        ((DerivedCategory.singleFunctor _ 0).map (a • 𝟙 (ordinaryFiniteConstant A Y))) ≫
        (ordinaryFiniteUnitPullback A f).hom =
      (ordinaryFiniteUnitPullback A f).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (a • 𝟙 (ordinaryFiniteConstant A X)) := by
  let : (ordinaryFinitePullback A f).Linear A :=
    linear_leftDerivedUpperStar (ModuleCat.{u + 1} A) f A
  exact kummer_linear_scalar_naturality A
    (DerivedCategory.singleFunctor _ 0) (ordinaryFinitePullback A f)
    (DerivedCategory.singleFunctor _ 0)
    (ordinaryFiniteConstant A Y) (ordinaryFiniteConstant A X)
    (ordinaryFiniteUnitPullback A f).hom a

/-- Scalar faithfulness of the actual Kummer class implies scalar faithfulness
of its specified Chern pushforward under the canonical derived adjunction.
Source: blueprint lemma-cohomology-projective-line-trace, the geometric Chern component.
(auxiliary; not a blueprint node).

Proof: linearity of inverse image and of the single functors makes the constant
comparison commute with scalar multiplication. Transpose an annihilated scalar
multiple through the adjunction defining the Chern pushforward. Naturality and
injectivity of its hom equivalence show that the same scalar annihilates the
original representative. Apply ordinaryFiniteClass_scalar_faithful to the actual
Kummer class specified by the Chern condition. -/
theorem ordinaryFiniteP1ChernPushforward_scalar_faithful
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S hP c)
    (hκ : Function.Injective (fun a : A ↦ Sheaf.H.map
      ((moduleAbelianForget A (ProjectiveLine S)).map
        (a • 𝟙 (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA))) 2
      (ordinaryFiniteP1KummerClass A N hA S hP))) :
    ∀ a : A, (DerivedCategory.singleFunctor _ 0).map
        (a • 𝟙 (ordinaryFiniteConstant A S)) ≫
      ordinaryFiniteP1ChernPushforward A N hA S c = 0 → a = 0 := by
  unfold ordinaryFiniteP1ChernSpec at hc
  unfold ordinaryFiniteP1ChernPushforward ordinaryFinitePushforward
  let f := ProjectiveLine S ↘ S
  let : (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.Additive :=
    additive_rightDerivedLowerStar (ModuleCat.{u + 1} A) f
  intro a ha
  apply ordinaryFiniteClass_scalar_faithful A (ProjectiveLine S)
    (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) c _ hc hκ a
  exact kummer_adj_precomp_zero _ _ (derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) f) (ordinaryFiniteUnitPullback A f) _ _
      (kummer_unit_scalar_naturality A f a) c ha

end AlgebraicGeometry.Etale
