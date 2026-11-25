/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! Generic transport of a section equation through an endofunctor. -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.RationalP1

/-- Data expressing compatibility of a pair of section comparisons with a pair of
endofunctor comparisons. -/
structure PullSectionTransportData
    {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} {G : D ⥤ C}
    {s₁ : F₁ ⋙ G ≅ 𝟭 C} {s₂ : F₂ ⋙ G ≅ 𝟭 C}
    (T : C ⥤ C) (U : D ⥤ D) (M : C)
    (e₁ : F₁.obj (T.obj M) ≅ U.obj (F₁.obj M))
    (e₂ : F₂.obj (T.obj M) ≅ U.obj (F₂.obj M))
    (b : F₁.obj M ≅ F₂.obj M) where
  d₁ : G.obj (U.obj (F₁.obj M)) ≅ T.obj (G.obj (F₁.obj M))
  d₂ : G.obj (U.obj (F₂.obj M)) ≅ T.obj (G.obj (F₂.obj M))
  h₁ : G.map e₁.inv ≫ s₁.hom.app (T.obj M) =
    d₁.hom ≫ T.map (s₁.hom.app M)
  h₂ : G.map e₂.hom ≫ d₂.hom ≫ T.map (s₂.hom.app M) =
    s₂.hom.app (T.obj M)
  hb : G.map e₂.hom ≫ G.map (U.map b.inv) ≫ d₁.hom ≫ T.map (s₁.hom.app M) =
    G.map e₂.hom ≫ d₂.hom ≫ T.map (G.map b.inv) ≫ T.map (s₁.hom.app M)

/-- Transport a section equation through a specified comparison of endofunctors.

The maps `d₁` and `d₂` compare applying `G` after `U` with applying `T` after `G`.
The hypotheses record the two section compatibilities and the compatibility of `b`.
The conclusion is the elementary categorical calculation used for the Tate-line factor.
-/
theorem pull_section_transport
    {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} {G : D ⥤ C}
    {s₁ : F₁ ⋙ G ≅ 𝟭 C} {s₂ : F₂ ⋙ G ≅ 𝟭 C}
    (T : C ⥤ C) (U : D ⥤ D) (M : C)
    (e₁ : F₁.obj (T.obj M) ≅ U.obj (F₁.obj M))
    (e₂ : F₂.obj (T.obj M) ≅ U.obj (F₂.obj M))
    (b : F₁.obj M ≅ F₂.obj M)
    (data : PullSectionTransportData (G := G) (s₁ := s₁) (s₂ := s₂) T U M e₁ e₂ b)
    (hbase : G.map b.inv ≫ s₁.hom.app M = s₂.hom.app M) :
    G.map (e₁ ≪≫ U.mapIso b ≪≫ e₂.symm).inv ≫ s₁.hom.app (T.obj M) =
      s₂.hom.app (T.obj M)  := by
  rw [Iso.trans_inv, Iso.trans_inv]
  simp only [Iso.symm_inv, Functor.mapIso_inv, Functor.map_comp]
  calc
    ((G.map e₂.hom ≫ G.map (U.map b.inv)) ≫ G.map e₁.inv) ≫ s₁.hom.app (T.obj M) =
        G.map e₂.hom ≫ G.map (U.map b.inv) ≫ data.d₁.hom ≫ T.map (s₁.hom.app M) := by
      simp only [Category.assoc]
      rw [data.h₁]
    _ = G.map e₂.hom ≫ (data.d₂.hom ≫ T.map (G.map b.inv)) ≫ T.map (s₁.hom.app M) := by
      simpa only [Category.assoc] using data.hb
    _ = G.map e₂.hom ≫ data.d₂.hom ≫ T.map (G.map b.inv ≫ s₁.hom.app M) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = G.map e₂.hom ≫ data.d₂.hom ≫ T.map (s₂.hom.app M) := by rw [hbase]
    _ = s₂.hom.app (T.obj M) := data.h₂

end AlgebraicGeometry.ProEtale.RationalP1
