/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Composition of inverse mates

Source: the mates correspondence, Mathlib CategoryTheory/Adjunction/Mates.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u₀ u₁ u₂ u₃ u₄ u₅ v₀ v₁ v₂ v₃ v₄ v₅
open CategoryTheory

namespace CategoryTheory

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂}
  {B₀ : Type u₃} {B₁ : Type u₄} {B₂ : Type u₅}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂]
  [Category.{v₃} B₀] [Category.{v₄} B₁] [Category.{v₅} B₂]
  {E₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} (a₀ : E₀ ⊣ R₀)
  {E₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} (a₁ : E₁ ⊣ R₁)
  {E₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂} (a₂ : E₂ ⊣ R₂)
  {F : A₀ ⥤ A₁} {G : A₁ ⥤ A₂} {H : A₀ ⥤ A₂}
  {F' : B₀ ⥤ B₁} {G' : B₁ ⥤ B₂} {H' : B₀ ⥤ B₂}
  (qf : R₀ ⋙ F ⟶ F' ⋙ R₁) (qg : R₁ ⋙ G ⟶ G' ⋙ R₂)
  (qh : R₀ ⋙ H ⟶ H' ⋙ R₂) (c : H ⟶ F ⋙ G) (c' : H' ⟶ F' ⋙ G')

/-- Inverse mates preserve a pasted square, including the two comparison maps.
Source: Mathlib `unit_mateEquiv_symm` and naturality of the unit.
(blueprint: new-integral-residue-mate-pasting)

Proof. Transpose the desired equation under the last adjunction. Expand the three
transposes with `unit_mateEquiv_symm`. Move units through the comparison maps by
naturality, use the given restriction-square composition equation, and apply the
composite unit equation for the last square. Injectivity of the adjunction hom
bijection gives the result. -/
theorem inverseMate_pasting
    (hq : ∀ N : B₀,
      c.app (R₀.obj N) ≫ G.map (qf.app N) ≫ qg.app (F'.obj N) =
        qh.app N ≫ R₂.map (c'.app N)) (K : A₀) :
    E₂.map (c.app K) ≫
        ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ qg)).app (F.obj K) ≫
        G'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qf)).app K) =
      ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qh)).app K ≫
        c'.app (E₀.obj K) := by
  let pf := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qf))
  let pg := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ qg))
  let ph := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qh))
  have hf := unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qf) K
  have hg := unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ qg) (F.obj K)
  have hh := unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qh) K
  change F.map (a₀.unit.app K) ≫ qf.app (E₀.obj K) =
    a₁.unit.app (F.obj K) ≫ R₁.map (pf.app K) at hf
  change G.map (a₁.unit.app (F.obj K)) ≫ qg.app (E₁.obj (F.obj K)) =
    a₂.unit.app (G.obj (F.obj K)) ≫ R₂.map (pg.app (F.obj K)) at hg
  change H.map (a₀.unit.app K) ≫ qh.app (E₀.obj K) =
    a₂.unit.app (H.obj K) ≫ R₂.map (ph.app K) at hh
  apply (a₂.homEquiv _ _).injective
  change a₂.unit.app (H.obj K) ≫
      R₂.map (E₂.map (c.app K) ≫ pg.app (F.obj K) ≫ G'.map (pf.app K)) =
    a₂.unit.app (H.obj K) ≫ R₂.map (ph.app K ≫ c'.app (E₀.obj K))
  simp only [Functor.map_comp, ← Category.assoc]
  have hu := a₂.unit.naturality (c.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  rw [← hu]
  simp only [Category.assoc, Functor.comp_obj]
  rw [← Category.assoc (a₂.unit.app (G.obj (F.obj K)))
    (R₂.map (pg.app (F.obj K))) (R₂.map (G'.map (pf.app K)))]
  rw [← hg]
  have hn := qg.naturality (pf.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← hn]
  rw [← G.map_comp_assoc, ← hf, G.map_comp]
  have hc := c.naturality (a₀.unit.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hc
  simp only [Category.assoc]
  rw [← reassoc_of% hc]
  rw [hq]
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ R₂.map (c'.app (E₀.obj K))) hh

end CategoryTheory
