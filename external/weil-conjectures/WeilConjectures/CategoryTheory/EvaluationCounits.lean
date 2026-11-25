/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Evaluation comparisons determined by the counit

Source: current blueprint proposition-sp-tower-geometric, final evaluation paragraph.
(blueprint: lem-sp-evaluation-counits-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {Cn : Type u₃} [Category.{v₃} Cn] {Dn : Type u₄} [Category.{v₄} Dn]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {Fn : Cn ⥤ Dn} {Gn : Dn ⥤ Cn} (finite : Fn ⊣ Gn)
  (evX : C ⥤ Cn) (evY : D ⥤ Dn) (support : F ⋙ evY ≅ evX ⋙ Fn)
  (comparison : ∀ K : D, evX.obj (G.obj K) ≅ Gn.obj (evY.obj K))
  (counit : ∀ K : D,
    support.inv.app (G.obj K) ≫ evY.map (adj.counit.app K) =
      Fn.map (comparison K).hom ≫ finite.counit.app (evY.obj K))

include adj finite support counit in
/-- The counit equation forces naturality of the finite right-adjoint comparisons.
Source: blueprint proposition-sp-tower-geometric, final evaluation paragraph.
Proof: transpose by the finite adjunction and use naturality of the two counits and
of the compact-support comparison. Injectivity of transposition concludes.
(blueprint: lem-sp-evaluation-counits-adjunction) -/
theorem evaluationCounit_naturality {K L : D} (f : K ⟶ L) :
    evX.map (G.map f) ≫ (comparison L).hom =
      (comparison K).hom ≫ Gn.map (evY.map f) := by
  apply (finite.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Fn.map_comp, Category.assoc]
  rw [← counit L]
  have hs := support.inv.naturality (G.map f)
  dsimp only [Functor.comp_map] at hs
  rw [← Category.assoc, hs, Category.assoc]
  change support.inv.app (G.obj K) ≫
      evY.map (F.map (G.map f)) ≫ evY.map (adj.counit.app L) = _
  have hn := adj.counit.naturality f
  change F.map (G.map f) ≫ adj.counit.app L = adj.counit.app K ≫ f at hn
  rw [← evY.map_comp, hn, evY.map_comp, ← Category.assoc, counit K]
  simp only [Category.assoc]
  have hf := finite.counit.naturality (evY.map f)
  change Fn.map (Gn.map (evY.map f)) ≫ finite.counit.app (evY.obj L) =
    finite.counit.app (evY.obj K) ≫ evY.map f at hf
  exact congrArg (fun z ↦ Fn.map (comparison K).hom ≫ z) hf.symm

/-- An objectwise counit-preserving identification is a natural evaluation comparison.
Source: blueprint proposition-sp-tower-geometric, evaluation and uniqueness.
(blueprint: lem-sp-evaluation-counits-adjunction) -/
def evaluationCounitComparison : G ⋙ evX ≅ evY ⋙ Gn :=
  NatIso.ofComponents comparison (fun f ↦
    evaluationCounit_naturality adj finite evX evY support comparison counit f)

/-- Counit-preserving evaluation comparisons also preserve the unit.
Source: blueprint proposition-sp-tower-geometric, final paragraph.
Proof: transposition by the finite adjunction is injective. On the left it gives
finite pushforward of the evaluated unit, followed by the evaluated tower counit,
conjugated by the support comparison. Naturality of that comparison and the tower
triangle identity reduce this to the identity. This is the transpose of the finite
unit. Naturality of the comparison follows in the same way from naturality of both
counits; no faithfulness of evaluation on derived morphisms is assumed.
(blueprint: lem-sp-evaluation-counits-adjunction) -/
theorem evaluationCounitComparison_unit (M : C) :
    evX.map (adj.unit.app M) ≫
      (evaluationCounitComparison adj finite evX evY support comparison counit).hom.app
        (F.obj M) ≫ Gn.map (support.hom.app M) =
      finite.unit.app (evX.obj M) := by
  apply (finite.homEquiv _ _).symm.injective
  change (finite.homEquiv (evX.obj M) (Fn.obj (evX.obj M))).symm _ =
    (finite.homEquiv (evX.obj M) (Fn.obj (evX.obj M))).symm _
  rw [finite.homEquiv_symm_unit]
  change Fn.map (evX.map (adj.unit.app M) ≫ (comparison (F.obj M)).hom ≫
      Gn.map (support.hom.app M)) ≫ finite.counit.app _ = 𝟙 _
  simp only [Fn.map_comp, Category.assoc]
  have hs := support.inv.naturality (adj.unit.app M)
  dsimp only [Functor.comp_map] at hs
  have hf := finite.counit.naturality (support.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map,
    Functor.id_obj] at hf hs
  change Fn.map (Gn.map (support.hom.app M)) ≫
      finite.counit.app (Fn.obj (evX.obj M)) =
    finite.counit.app (evY.obj (F.obj M)) ≫ support.hom.app M at hf
  change Fn.map (evX.map (adj.unit.app M)) ≫
      Fn.map (comparison (F.obj M)).hom ≫
      Fn.map (Gn.map (support.hom.app M)) ≫
      finite.counit.app (Fn.obj (evX.obj M)) = 𝟙 _
  rw [hf]
  have hco := congrArg (fun z ↦ z ≫ support.hom.app M) (counit (F.obj M))
  simp only [Category.assoc] at hco
  rw [← hco, ← Category.assoc, hs]
  change (support.inv.app M ≫ evY.map (F.map (adj.unit.app M))) ≫
      evY.map (adj.counit.app (F.obj M)) ≫ support.hom.app M = 𝟙 _
  have ht := adj.left_triangle_components M
  simp only [Category.assoc]
  rw [← evY.map_comp_assoc, ht, evY.map_id]
  simp

end CategoryTheory
