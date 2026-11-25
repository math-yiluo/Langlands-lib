/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Restricting an oriented dualizing comparison

The formal naturality calculation in Step 4(ii) of the regular-immersion proof,
before applying co-projection or cancelling Tate factors.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(ii).
(blueprint: lem-pur-regular-oriented-restriction-naturality).
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

namespace CategoryTheory

/-- Naturality transports the oriented comparison once the dualizing and orientation
squares commute. Here `B` is the specified exceptional restriction map; `Cu` and
`Cv` keep the coefficient pullback identifications explicit.

Proof: substitute the orientation identity for `PU`, cancel `Cu` with its inverse,
and use naturality of `B` at `PX.hom`. The dualizing square then replaces the middle
word by `Ev.hom` followed by the pullback of `b.hom`. The orientation identity for
`PV` implies `PV.inv ≫ Ev.hom = Cv.inv ≫ T.map PZ.inv`. Substitution and functoriality
of `T` give the result. No tensor, invertibility detection, or choice of maps is used.
Source: regular-immersion proof Step 4(ii), equation (3), refining the item's
fourth proof step (blueprint: lem-pur-regular-oriented-restriction-naturality). -/
theorem regularOrientedRestrictionNaturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (S : C ⥤ D) (G : C ⥤ E) (H : D ⥤ F) (T : E ⥤ F)
    (B : S ⋙ H ⟶ G ⋙ T)
    {WX TX : C} {WU TU : D} {WZ TZ : E} {WV TV : F}
    (b : WZ ≅ G.obj WX) (bU : WV ≅ H.obj WU)
    (Eu : WU ≅ S.obj WX) (Ev : WV ≅ T.obj WZ)
    (PX : WX ≅ TX) (PZ : WZ ≅ TZ) (PU : WU ≅ TU) (PV : WV ≅ TV)
    (Cu : S.obj TX ≅ TU) (Cv : T.obj TZ ≅ TV)
    (hb : bU.hom ≫ H.map Eu.hom ≫ B.app WX = Ev.hom ≫ T.map b.hom)
    (hu : PU.hom = Eu.hom ≫ S.map PX.hom ≫ Cu.hom)
    (hv : PV.hom = Ev.hom ≫ T.map PZ.hom ≫ Cv.hom) :
    PV.inv ≫ bU.hom ≫ H.map PU.hom ≫ H.map Cu.inv ≫ B.app TX =
      Cv.inv ≫ T.map (PZ.inv ≫ b.hom ≫ G.map PX.hom) := by
  have hV : PV.inv ≫ Ev.hom = Cv.inv ≫ T.map PZ.inv := by
    apply (cancel_epi PV.hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [hv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← T.map_comp, Iso.hom_inv_id,
      T.map_id, Category.comp_id]
  have hU : PU.hom ≫ Cu.inv = Eu.hom ≫ S.map PX.hom := by
    rw [hu]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← H.map_comp_assoc, hU, H.map_comp]
  simp only [Category.assoc]
  have hn : H.map (S.map PX.hom) ≫ B.app TX =
      B.app WX ≫ T.map (G.map PX.hom) := B.naturality PX.hom
  rw [hn]
  rw [reassoc_of% hb]
  calc
    _ = (PV.inv ≫ Ev.hom) ≫ T.map b.hom ≫ T.map (G.map PX.hom) := by
      simp only [Category.assoc]
    _ = _ := by rw [hV]; simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
