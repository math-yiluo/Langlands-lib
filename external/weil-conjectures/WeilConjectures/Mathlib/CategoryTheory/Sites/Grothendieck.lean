/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Cardinality of the multicospan of a cover

If the category `C` has fewer than `κ` arrows, for a regular cardinal `κ`, then so do the
arrows `S.Arrow` and the relations `S.Relation` of a cover `S : J.Cover X`
(`CategoryTheory.GrothendieckTopology.Cover.hasCardinalLT_arrow` and
`CategoryTheory.GrothendieckTopology.Cover.hasCardinalLT_relation`), and hence so does the walking
multicospan `WalkingMulticospan S.shape` indexing the sheaf condition
(`CategoryTheory.GrothendieckTopology.Cover.hasCardinalLT_arrow_walkingMulticospan`).

See also `CategoryTheory.preservesColimitsOfShape_lim_of_isDetector`.

We also record how the canonical map `S.toMultiequalizer P` interacts with the projections of
the multiequalizer (`CategoryTheory.GrothendieckTopology.Cover.toMultiequalizer_ι`).
-/

@[expose] public section

universe w v u

namespace CategoryTheory.GrothendieckTopology.Cover

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {X : C}

-- In this namespace `Arrow` refers to `GrothendieckTopology.Cover.Arrow`, so the arrow
-- category is written `CategoryTheory.Arrow`.

/-- The arrows of a cover `S` are the pairs of an object `Y` and a morphism `f : Y ⟶ X`
in `S`. -/
@[simps]
def arrowEquivSigma (S : J.Cover X) :
    S.Arrow ≃ Σ Y : C, { f : Y ⟶ X // S f } where
  toFun I := ⟨I.Y, I.f, I.hf⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩

/-- A relation between two arrows `I₁ I₂` of a cover is an object `Z` with a pair of
morphisms `g₁ : Z ⟶ I₁.Y`, `g₂ : Z ⟶ I₂.Y` such that `g₁ ≫ I₁.f = g₂ ≫ I₂.f`. -/
@[simps]
def Arrow.relationEquivSigma {S : J.Cover X} (I₁ I₂ : S.Arrow) :
    I₁.Relation I₂ ≃
      Σ Z : C, { g : (Z ⟶ I₁.Y) × (Z ⟶ I₂.Y) // g.1 ≫ I₁.f = g.2 ≫ I₂.f } where
  toFun r := ⟨r.Z, (r.g₁, r.g₂), r.w⟩
  invFun p := ⟨p.1, p.2.1.1, p.2.1.2, p.2.2⟩

/-- The relations of a cover `S` are the relations between pairs of arrows of `S`. -/
@[simps]
def relationEquivSigma (S : J.Cover X) :
    S.Relation ≃ Σ I : S.Arrow × S.Arrow, I.1.Relation I.2 where
  toFun r := ⟨(r.fst, r.snd), r.r⟩
  invFun p := ⟨p.2⟩

/-- If `C` has fewer than `κ` arrows for a regular cardinal `κ`, then so does any cover
`S : J.Cover X`. Regularity of `κ` is used to bound the sigma type over the objects of `C`. -/
lemma hasCardinalLT_arrow (S : J.Cover X) {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hC : HasCardinalLT (CategoryTheory.Arrow C) κ) : HasCardinalLT S.Arrow κ :=
  (hasCardinalLT_iff_of_equiv S.arrowEquivSigma κ).2
    (hasCardinalLT_sigma _ κ (hasCardinalLT_of_hasCardinalLT_arrow hC) fun Y ↦
      (hasCardinalLT_hom_of_hasCardinalLT_arrow hC Y X).of_injective _ Subtype.val_injective)

/-- If `C` has fewer than `κ` arrows for a regular cardinal `κ`, then so do the relations of
any cover `S : J.Cover X`. Regularity of `κ` is used to bound the sigma types involved. -/
lemma hasCardinalLT_relation (S : J.Cover X) {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hC : HasCardinalLT (CategoryTheory.Arrow C) κ) : HasCardinalLT S.Relation κ := by
  have hκ : Cardinal.aleph0 ≤ κ := (Fact.out : κ.IsRegular).aleph0_le
  have hS := S.hasCardinalLT_arrow hC
  refine (hasCardinalLT_iff_of_equiv S.relationEquivSigma κ).2
    (hasCardinalLT_sigma _ κ (hasCardinalLT_prod hκ hS hS) fun I ↦ ?_)
  refine (hasCardinalLT_iff_of_equiv (Arrow.relationEquivSigma I.1 I.2) κ).2
    (hasCardinalLT_sigma _ κ (hasCardinalLT_of_hasCardinalLT_arrow hC) fun Z ↦ ?_)
  exact (hasCardinalLT_prod hκ (hasCardinalLT_hom_of_hasCardinalLT_arrow hC _ _)
    (hasCardinalLT_hom_of_hasCardinalLT_arrow hC _ _)).of_injective _ Subtype.val_injective

/-- If `C` has fewer than `κ` arrows for a regular cardinal `κ`, then so does the walking
multicospan indexing the sheaf condition for a cover `S : J.Cover X`. Regularity of `κ` is
used to bound the arrows and relations of `S`. -/
lemma hasCardinalLT_arrow_walkingMulticospan (S : J.Cover X)
    {κ : Cardinal.{w}} [Fact κ.IsRegular] (hC : HasCardinalLT (CategoryTheory.Arrow C) κ) :
    HasCardinalLT (CategoryTheory.Arrow (WalkingMulticospan S.shape)) κ :=
  Limits.hasCardinalLT_arrow_walkingMulticospan (S.hasCardinalLT_arrow hC)
    (S.hasCardinalLT_relation hC) (Fact.out : κ.IsRegular).aleph0_le

/-- The `I`-th component of the canonical map `P(X) ⟶ multiequalizer (S.index P)` is the
restriction `P.map I.f.op : P(X) ⟶ P(I.Y)`. -/
@[reassoc (attr := simp)]
lemma toMultiequalizer_ι {D : Type*} [Category* D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D)
    [HasMultiequalizer (S.index P)] (I : S.Arrow) :
    S.toMultiequalizer P ≫ Multiequalizer.ι (S.index P) I = P.map I.f.op :=
  Multiequalizer.lift_ι _ _ _ _ _

end CategoryTheory.GrothendieckTopology.Cover
