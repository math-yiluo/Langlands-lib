/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Bases through the unit of an adjunction, along an isomorphism of left adjoints

For an adjunction `adj : L ⊣ G` and natural endomorphisms `σ i` of the identity of the target,
consider the map `K^{⊕ι} ⟶ G L K`, `(x_i) ↦ Σ G (σ i) (η x_i)`. Transporting the adjunction along
an isomorphism `L ≅ L'` (`Adjunction.ofNatIsoLeft`) does not change whether this map is an
isomorphism (`Adjunction.isIso_biproductDesc_ofNatIsoLeft_unit`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
  {L L' : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (e : L ≅ L')
  {ι : Type*} (σ : ι → (𝟭 D ⟶ 𝟭 D)) (K : C) [HasBiproduct fun _ : ι ↦ K]

/-- The map `K^{⊕ι} ⟶ G L' K` of the transported adjunction is the one of `adj` followed by
`G e`. -/
lemma biproductDesc_ofNatIsoLeft_unit :
    (biproduct.desc (f := fun _ : ι ↦ K) fun i ↦ (adj.ofNatIsoLeft e).unit.app K ≫
      G.map ((σ i).app (L'.obj K))) =
      (biproduct.desc (f := fun _ : ι ↦ K) fun i ↦ adj.unit.app K ≫ G.map ((σ i).app (L.obj K))) ≫
        G.map (e.hom.app K) := by
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  rw [biproduct.ι_desc, biproduct.ι_desc_assoc, ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Category.assoc, Category.assoc, ← G.map_comp, ← G.map_comp]
  exact congrArg (fun f ↦ adj.unit.app K ≫ G.map f) ((σ i).naturality (e.hom.app K))

/-- The map `K^{⊕ι} ⟶ G L' K` of the transported adjunction is an isomorphism if the one of
`adj` is. -/
lemma isIso_biproductDesc_ofNatIsoLeft_unit
    (h : IsIso (biproduct.desc (f := fun _ : ι ↦ K) fun i ↦ adj.unit.app K ≫
      G.map ((σ i).app (L.obj K)))) :
    IsIso (biproduct.desc (f := fun _ : ι ↦ K) fun i ↦ (adj.ofNatIsoLeft e).unit.app K ≫
      G.map ((σ i).app (L'.obj K))) := by
  rw [biproductDesc_ofNatIsoLeft_unit]
  infer_instance

end CategoryTheory.Adjunction
