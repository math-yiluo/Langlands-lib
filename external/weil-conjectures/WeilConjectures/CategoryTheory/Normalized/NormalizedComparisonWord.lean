/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.NatIso
/-! # An explicit six-factor normalized word -/
@[expose] public section
set_option autoImplicit false
namespace CategoryTheory
/-- Seven invertibility claims and the specified six-factor equality, with all objects
and arrows explicit so that geometric specializations share their category instances.
Source: lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: def-coef-normalized-comparison-word). -/
def NormalizedComparisonWord
    {C D : Type*} [Category C] [Category D] {U V : C}
    (i : U ⟶ V) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) (v : X₀ ⟶ X₆) : Prop :=
  IsIso i ∧ IsIso a ∧ IsIso b ∧ IsIso c ∧ IsIso d ∧ IsIso e ∧ IsIso f ∧
    a ≫ b ≫ c ≫ d ≫ e ≫ f = v
/-- Assemble a normalized word from its exact factors and equality.
Source: lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: def-coef-normalized-comparison-word). -/
theorem NormalizedComparisonWord.mk
    {C D : Type*} [Category C] [Category D] {U V : C}
    (i : U ⟶ V) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) (v : X₀ ⟶ X₆)
    [IsIso i] [IsIso a] [IsIso b] [IsIso c] [IsIso d] [IsIso e] [IsIso f]
    (h : a ≫ b ≫ c ≫ d ≫ e ≫ f = v) :
    NormalizedComparisonWord i a b c d e f v :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, h⟩
/-- Assemble the word with mapped isomorphisms and a contravariant Hom factor.
Source: lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: def-coef-normalized-comparison-word). -/
theorem NormalizedComparisonWord.of_maps
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    {U V : C} (i : U ⟶ V) [IsIso i] {P Q R : E}
    (b : F.obj U ⟶ G.obj P) [IsIso b]
    (c : P ⟶ Q) [IsIso c] (d : Q ⟶ R) [IsIso d]
    {Y Y' : D} (q : Y ⟶ Y') [IsIso q] (M : D)
    (e : G.obj R ⟶ (H.obj (Opposite.op Y')).obj M) [IsIso e]
    (v : F.obj V ⟶ (H.obj (Opposite.op Y)).obj M)
    (h : F.map (inv i) ≫ b ≫ G.map c ≫ G.map d ≫ e ≫ (H.map q.op).app M = v) :
    NormalizedComparisonWord i (F.map (inv i)) b (G.map c) (G.map d) e
      ((H.map q.op).app M) v :=
  NormalizedComparisonWord.mk _ _ _ _ _ _ _ _ h
/-- Cancel a mapped inverse from the exact functorial pairing equation.
Source: lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: lem-coef-locally-closed-pairing-cancellation). -/
theorem cancelMappedPairing
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) {U V : C} (i : U ⟶ V) [IsIso i]
    {P Q R : E} {T W : D} (b : F.obj U ⟶ G.obj P)
    (c : P ⟶ Q) (d : Q ⟶ R) (e : G.obj R ⟶ T) (f : T ⟶ W)
    (v : F.obj V ⟶ W)
    (h : b ≫ G.map (c ≫ d) ≫ e ≫ f = F.map i ≫ v) :
    F.map (inv i) ≫ b ≫ G.map c ≫ G.map d ≫ e ≫ f = v := by
  rw [Functor.map_inv, IsIso.inv_comp_eq]
  simpa only [Functor.map_comp, Category.assoc] using h
/-- The mapped comparison word, retaining its functors as parameters.
Source: lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: def-coef-normalized-comparison-word). -/
def MappedComparisonWord
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    {U V : C} (i : U ⟶ V) [IsIso i] {P Q R : E}
    (b : F.obj U ⟶ G.obj P) (c : P ⟶ Q) (d : Q ⟶ R)
    {Y Y' : D} (q : Y ⟶ Y') (M : D)
    (e : G.obj R ⟶ (H.obj (Opposite.op Y')).obj M)
    (v : F.obj V ⟶ (H.obj (Opposite.op Y)).obj M) : Prop :=
  NormalizedComparisonWord i (F.map (inv i)) b (G.map c) (G.map d) e
    ((H.map q.op).app M) v
/-- The equality part of the mapped comparison word.
Source: lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: def-coef-normalized-comparison-word). -/
def MappedComparisonEquation
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    {U V : C} (i : U ⟶ V) [IsIso i] {P Q R : E}
    (b : F.obj U ⟶ G.obj P) (c : P ⟶ Q) (d : Q ⟶ R)
    {Y Y' : D} (q : Y ⟶ Y') (M : D)
    (e : G.obj R ⟶ (H.obj (Opposite.op Y')).obj M)
    (v : F.obj V ⟶ (H.obj (Opposite.op Y)).obj M) : Prop :=
  F.map (inv i) ≫ b ≫ G.map c ≫ G.map d ≫ e ≫ (H.map q.op).app M = v
/-- Construct the mapped word using only isomorphisms of the unmapped factors.
Source: lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: def-coef-normalized-comparison-word). -/
theorem MappedComparisonWord.mk
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    {U V : C} (i : U ⟶ V) [IsIso i] {P Q R : E}
    (b : F.obj U ⟶ G.obj P) (c : P ⟶ Q) (d : Q ⟶ R)
    {Y Y' : D} (q : Y ⟶ Y') (M : D)
    (e : G.obj R ⟶ (H.obj (Opposite.op Y')).obj M)
    (v : F.obj V ⟶ (H.obj (Opposite.op Y)).obj M)
    [IsIso b] [IsIso c] [IsIso d] [IsIso q] [IsIso e]
    (h : MappedComparisonEquation F G H i b c d q M e v) :
    MappedComparisonWord F G H i b c d q M e v :=
  NormalizedComparisonWord.of_maps F G H i b c d q M e v h
end CategoryTheory
