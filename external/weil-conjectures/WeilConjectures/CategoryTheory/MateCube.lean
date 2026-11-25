/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! The generic inverse-mate cube, retained from TensorPullbackSquare. -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory

/-- Four inverse mate comparisons transport a commutative cube.
Source: Mathlib's adjunction mate formulas and the final tensor-compatibility
paragraph of the latest blueprint's lemma-sp-reduction--1.
(blueprint: lem-sp-scalar-mate-cube)
Proof: transpose both composites by the last adjunction. Use its unit naturality
and the four unit_mateEquiv_symm equations. Naturality of qI moves the first
inverse mate, and naturality of c moves the initial unit. Substitute hc. On the
other side naturality of qH moves the remaining inverse mate. Functoriality and
associativity identify the transposes, and homEquiv injectivity gives equality. -/
theorem scalarMateCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ M, c.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.app M))
    (N : C₀) :
    S₃.map (c.app N) ≫
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).app (G.obj N) ≫
        I'.map (((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).app N) =
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).app (J.obj N) ≫
        H'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).app N) ≫
        d.app (S₀.obj N) := by
  let lJ := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ))
  let lH := ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH))
  let lG := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG))
  let lI := ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI))
  have hj (K : C₀) : J.map (a₀.unit.app K) ≫ qJ.app (S₀.obj K) =
      a₁.unit.app (J.obj K) ≫ R₁.map (lJ.app K) :=
    unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qJ) K
  have hh (K : C₁) : H.map (a₁.unit.app K) ≫ qH.app (S₁.obj K) =
      a₃.unit.app (H.obj K) ≫ R₃.map (lH.app K) :=
    unit_mateEquiv_symm a₁ a₃ (TwoSquare.mk _ _ _ _ qH) K
  have hg (K : C₀) : G.map (a₀.unit.app K) ≫ qG.app (S₀.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (lG.app K) :=
    unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qG) K
  have hi (K : C₂) : I.map (a₂.unit.app K) ≫ qI.app (S₂.obj K) =
      a₃.unit.app (I.obj K) ≫ R₃.map (lI.app K) :=
    unit_mateEquiv_symm a₂ a₃ (TwoSquare.mk _ _ _ _ qI) K
  change S₃.map (c.app N) ≫ lI.app (G.obj N) ≫ I'.map (lG.app N) =
    lH.app (J.obj N) ≫ H'.map (lJ.app N) ≫ d.app (S₀.obj N)
  apply (a₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := a₃.unit.naturality (c.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← reassoc_of% (hi (G.obj N))]
  have hq := qI.naturality (lG.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← I.map_comp_assoc, ← hg, I.map_comp]
  have hcn := c.naturality (a₀.unit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcn
  simp only [Category.assoc, Functor.id_obj] at hcn ⊢
  rw [← reassoc_of% hcn, hc]
  rw [← reassoc_of% (hh (J.obj N))]
  have hqn := qH.naturality (lJ.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqn
  rw [← reassoc_of% hqn, ← H.map_comp_assoc, hj]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
