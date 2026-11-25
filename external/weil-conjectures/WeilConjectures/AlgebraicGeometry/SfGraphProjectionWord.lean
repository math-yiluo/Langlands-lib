/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-! # Successive projection on explicit proper/open/proper factors

Source: Stacks Tags 0B56 and 0GL1; canonical pullback composition from Tag 0E48.
The coefficient category stays a parameter throughout the calculation, so the map
and its factorization share their derived-category structures.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false

attribute [local implicit_reducible] CategoryTheory.catToReflQuiver

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] Compactification.comp
attribute [local irreducible] projectionMapOfCompactification rightDerivedLowerStarComp
  openImmersionLowerShriekLowerStarExchange mapDerivedCategoryOpenImmersionLowerShriekComp
  mapDerivedCategoryOpenImmersionLowerShriekCongr

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedTensor rightDerivedLowerStarProjectionMap
  derivedOpenImmersionLowerShriekProjectionIso leftDerivedUpperStarComp
  upperStar lowerStar openImmersionLowerShriek

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
  {FC : B → B → Type*} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Compose the three canonical projection maps and the inverse pullback compositor.
Source: Stacks Tags 0B56, 0GL1 and 0F7B; explicit graph-word projection
(auxiliary; not a blueprint node). -/
noncomputable def sfGraphProjectionWord
    {X W P Y : Scheme.{u}} (a : X ⟶ W) (e : W ⟶ P) (p : P ⟶ Y)
    [IsProper a] [IsOpenImmersion e] [IsProper p] (f : X ⟶ Y)
    (hf : a ≫ e ≫ p = f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((derivedTensor B Y).obj (((lowerStar B a).rightDerivedFunctor ⋙
      (openImmersionLowerShriek B e).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).obj M)).obj K ⟶
      ((lowerStar B a).rightDerivedFunctor ⋙
      (openImmersionLowerShriek B e).mapDerivedCategory ⋙ (lowerStar B p).rightDerivedFunctor).obj
        (((derivedTensor B X).obj M).obj ((upperStar B f).leftDerivedFunctor.obj K)) := by
  let R := (lowerStar B p).rightDerivedFunctor
  let J := (openImmersionLowerShriek B e).mapDerivedCategory
  let S := (lowerStar B a).rightDerivedFunctor
  let Lp := (upperStar B p).leftDerivedFunctor
  let Le := (upperStar B e).leftDerivedFunctor
  exact ((rightDerivedLowerStarProjectionMap B p).app (J.obj (S.obj M))).app K ≫
    R.map (((derivedOpenImmersionLowerShriekProjectionIso B e).inv.app
      (S.obj M)).app (Lp.obj K)) ≫
    R.map (J.map (((rightDerivedLowerStarProjectionMap B a).app M).app
      (Le.obj (Lp.obj K)))) ≫
    R.map (J.map (S.map (((derivedTensor B X).obj M).map
      ((leftDerivedUpperStarComp B a e).inv.app (Lp.obj K) ≫
        (leftDerivedUpperStarComp B (a ≫ e) p f
          ((Category.assoc a e p).trans hf).symm).inv.app K))))

private theorem prefix_coefficient_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S : C ⥤ D) (F : D ⥤ E)
    {P Q : D} {N N' N'' : C} {V W : E}
    (p₀ : V ⟶ W) (p₁ : W ⟶ F.obj P)
    (v : P ⟶ Q) (a : Q ⟶ S.obj N) (b : P ⟶ S.obj N')
    (w : N' ⟶ N) (z : N ⟶ N'') (d : N' ⟶ N'')
    (hn : v ≫ a = b ≫ S.map w) (hc : w ≫ z = d) :
    (p₀ ≫ p₁ ≫ F.map v) ≫ F.map a ≫ F.map (S.map z) =
      p₀ ≫ p₁ ≫ F.map b ≫ F.map (S.map d) := by
  have h : v ≫ a ≫ S.map z = b ≫ S.map d := by
    rw [reassoc_of% hn, ← S.map_comp, hc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun q ↦ p₀ ≫ p₁ ≫ F.map q) h

private theorem map_composite_eq
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (h : a ≫ b = c) : T.map a ≫ T.map b = T.map c := by
  rw [← T.map_comp, h]

private theorem prefix_factor_congr
    {C : Type*} [Category C] {A B D E : C}
    {p p' : A ⟶ B} {q : B ⟶ D} {r : D ⟶ E} {s : A ⟶ E}
    (hp : p = p') (h : p' ≫ q ≫ r = s) : p ≫ q ≫ r = s := by
  rw [hp]
  exact h

omit [HasSmallSiteSheafify B] in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem grouped_prefix_expansion
    {X W Y : Scheme.{u}} {f₀ : W ⟶ Y} (c : Compactification f₀)
    (a : X ⟶ W) [IsProper a] (f : X ⟶ Y) (hf : f = a ≫ f₀)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    let S := (lowerStar B a).rightDerivedFunctor
    let R := (lowerStar B c.g).rightDerivedFunctor
    let J := (openImmersionLowerShriek B c.i).mapDerivedCategory
    let F := rightDerivedLowerShriekOfCompactification B c
    ((projectionMapOfCompactification B c).app (S.obj M)).app K ≫
        F.map (((rightDerivedLowerStarProjectionMap B a).app M).app
          ((upperStar B f₀).leftDerivedFunctor.obj K)) ≫
        F.map (S.map (((derivedTensor B X).obj M).map
          ((leftDerivedUpperStarComp B a f₀ f hf).inv.app K))) =
      ((rightDerivedLowerStarProjectionMap B c.g).app
        (J.obj (S.obj M))).app K ≫
      R.map (((derivedOpenImmersionLowerShriekProjectionIso
        B c.i).inv.app (S.obj M)).app
          ((upperStar B c.g).leftDerivedFunctor.obj K)) ≫
      F.map (((rightDerivedLowerStarProjectionMap B a).app M).app
        ((upperStar B c.i).leftDerivedFunctor.obj
          ((upperStar B c.g).leftDerivedFunctor.obj K))) ≫
      F.map (S.map (((derivedTensor B X).obj M).map
        ((leftDerivedUpperStarComp B a c.i).inv.app
          ((upperStar B c.g).leftDerivedFunctor.obj K) ≫
        (leftDerivedUpperStarComp B (a ≫ c.i) c.g f
          (hf.trans ((congrArg (a ≫ ·) c.comm).trans
            (Category.assoc a c.i c.g).symm))).inv.app K))) := by
  intro S R J F
  have hn := properProjection_naturality_right B a M _ _
    ((leftDerivedUpperStarComp B c.i c.g f₀ c.comm).inv.app K)
  have hc := map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app
    B a c.i c.g (a ≫ c.i) f₀ f rfl c.comm
    (hf.trans ((congrArg (a ≫ ·) c.comm).trans
      (Category.assoc a c.i c.g).symm)) K
  have hcm := map_composite_eq ((derivedTensor B X).obj M) hc
  have he := projectionMapOfCompactification_explicit B c (S.obj M) K
  have hp := prefix_coefficient_paste S F
    (((rightDerivedLowerStarProjectionMap B c.g).app
      (J.obj (S.obj M))).app K)
    (R.map (((derivedOpenImmersionLowerShriekProjectionIso
      B c.i).inv.app (S.obj M)).app
        ((upperStar B c.g).leftDerivedFunctor.obj K)))
    _ _ _ _ _ _ hn hcm
  exact prefix_factor_congr he hp

omit [HasSmallSiteSheafify B] in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The successive projection factors through the compactification projection on Ra M.
Source: Stacks Tags 0B56 and 0GL1 and the canonical pullback associativity of Tag 0E48
(auxiliary; not a blueprint node).

Proof: expand the compactification projection into its proper projection, open tensor
comparison and inverse pullback compositor. Naturality of the proper projection for a
moves the inverse compositor through that projection. Inverse threefold pullback
associativity then identifies the two coefficient maps. Functoriality and associativity
paste these equalities. This uses no inverse of a projection map and has no boundedness
or quasi-compactness hypothesis.
-/
theorem sfGraphProjectionWord_proper_prefix
    {X W Y : Scheme.{u}} {f₀ : W ⟶ Y} (c : Compactification f₀)
    (a : X ⟶ W) [IsProper a] (f : X ⟶ Y) (hf : f = a ≫ f₀)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    let S := (lowerStar B a).rightDerivedFunctor
    let F := rightDerivedLowerShriekOfCompactification B c
    sfGraphProjectionWord B a c.i c.g f
      (by rw [← c.comm, ← hf]) M K =
      ((projectionMapOfCompactification B c).app (S.obj M)).app K ≫
        F.map (((rightDerivedLowerStarProjectionMap B a).app M).app
          ((upperStar B f₀).leftDerivedFunctor.obj K)) ≫
        F.map (S.map (((derivedTensor B X).obj M).map
          ((leftDerivedUpperStarComp B a f₀ f hf).inv.app K))) := by
  intro S F
  exact (grouped_prefix_expansion B c a f hf M K).symm

end AlgebraicGeometry.Etale
