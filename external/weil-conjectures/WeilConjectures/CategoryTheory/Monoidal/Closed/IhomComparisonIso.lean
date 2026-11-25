/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs along a lax monoidal functor, up to isomorphism

Let `G : C ⥤ D` be a lax monoidal functor between monoidal closed categories such that the
comparison map `G [A, B] ⟶ [G A, G B]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) is an
isomorphism. Given isomorphisms `G A ≅ A'` and `G B ≅ B'`, this file builds the isomorphism
`G [A, B] ≅ [A', B']` (`CategoryTheory.Functor.LaxMonoidal.mapIhomObjIso`) and shows that it is
compatible with evaluation (`CategoryTheory.Functor.LaxMonoidal.μ_comp_map_ev_comp_hom`):
```
  G A ⊗ G [A, B] ──────▶ A' ⊗ [A', B']
        │                       │
       μ│                       │ev
        ▼                       ▼
  G (A ⊗ [A, B]) ──G ev──▶ G B ──▶ B'
```
-/

@[expose] public section

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.LaxMonoidal]
  {A B : C} {A' B' : D} [IsIso ((ihomComparison G A).app B)]

/-- The isomorphism `G [A, B] ≅ [A', B']` induced by isomorphisms `e : G A ≅ A'` and
`d : G B ≅ B'`, when the comparison map `G [A, B] ⟶ [G A, G B]` is an isomorphism. -/
noncomputable def mapIhomObjIso (e : G.obj A ≅ A') (d : G.obj B ≅ B') :
    G.obj ((ihom A).obj B) ≅ (ihom A').obj B' :=
  asIso ((ihomComparison G A).app B) ≪≫ (ihom (G.obj A)).mapIso d ≪≫
    { hom := (pre e.inv).app B'
      inv := (pre e.hom).app B'
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← pre_map, e.hom_inv_id, pre_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id, NatTrans.id_app] }

lemma mapIhomObjIso_hom (e : G.obj A ≅ A') (d : G.obj B ≅ B') :
    (mapIhomObjIso G e d).hom = (ihomComparison G A).app B ≫
      (ihom (G.obj A)).map d.hom ≫ (pre e.inv).app B' :=
  rfl

/-- The isomorphism `G [A, B] ≅ [A', B']` of `mapIhomObjIso` is compatible with evaluation:
`G` of the evaluation `A ⊗ [A, B] ⟶ B`, after the tensorator and `d : G B ≅ B'`, is the evaluation
`A' ⊗ [A', B'] ⟶ B'` after `e ⊗ mapIhomObjIso G e d`. -/
lemma μ_comp_map_ev_comp_hom (e : G.obj A ≅ A') (d : G.obj B ≅ B') :
    μ G A ((ihom A).obj B) ≫ G.map ((ihom.ev A).app B) ≫ d.hom =
      (e.hom ⊗ₘ (mapIhomObjIso G e d).hom) ≫ (ihom.ev A').app B' := by
  rw [mapIhomObjIso_hom, tensorHom_def, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Category.assoc, Category.assoc,
    id_tensor_pre_app_comp_ev, whisker_exchange_assoc, whisker_exchange_assoc,
    ← comp_whiskerRight_assoc, e.hom_inv_id, id_whiskerRight, Category.id_comp,
    ihom.ev_naturality, ihomComparison_ev_assoc]

end CategoryTheory.Functor.LaxMonoidal
