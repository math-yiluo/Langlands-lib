/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap

/-! # Exchange and the specified completed pullback unit -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
open CategoryTheory
section
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]
  {F : C ⥤ D} {R : D ⥤ C} {P : E ⥤ H} {Q : H ⥤ E}
  {Cv B : C ⥤ E} {Cu T : D ⥤ H} {Lv : E ⥤ C} {Lu : H ⥤ D}

private lemma projection_unit (adj : F ⊣ R) (padj : P ⊣ Q)
    (χ : B ⋙ P ⟶ F ⋙ T) (K : C) :
    B.map (adj.unit.app K) ≫
      (padj.homEquiv _ _)
        (χ.app (R.obj (F.obj K)) ≫ T.map (adj.counit.app (F.obj K))) =
      padj.unit.app (B.obj K) ≫ Q.map (χ.app K) := by
  rw [← padj.homEquiv_naturality_left]
  rw [← Category.assoc]
  have hn := χ.naturality (adj.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [hn]
  simp only [Functor.id_obj, Category.assoc, ← T.map_comp, adj.left_triangle_components,
    T.map_id, Category.comp_id, Adjunction.homEquiv_unit]

end
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
