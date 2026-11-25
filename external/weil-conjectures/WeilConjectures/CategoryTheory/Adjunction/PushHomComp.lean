/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare

/-!
# Composition of the mates `Adjunction.pushHomOfComapIso`

Consider three adjunctions `Lᵢ ⊣ Rᵢ` on each of two sides `X` and `Y` (extension and restriction
of scalars along `a`, `b` and `c`, where `c` is the composite of `a` and `b`), functors
`P₁, P₂, P₃` from the `X` side to the `Y` side (the pushforwards over the three coefficient rings),
and isomorphisms `e_a : P₂ ⋙ R^Y_a ≅ R^X_a ⋙ P₁`, `e_b`, `e_c` (restriction of scalars commutes
with the pushforward). Suppose that the right adjoints compose, `κ : R_b ⋙ R_a ≅ R_c` on both
sides, and that `e_c` is the composite of `e_a` and `e_b` up to `κ`. Then the mate
`P₁ ⋙ L^Y_c ⟶ L^X_c ⋙ P₃` of `e_c` (`Adjunction.pushHomOfComapIso`) is the composite of the mates
of `e_a` and `e_b`, up to the conjugates `θ : L_c ≅ L_a ⋙ L_b` of `κ`
(`Adjunction.pushHomOfComapIso_app_eq_comp`). This is the compatibility of the (Push) comparison
with the composition of coefficient changes; it follows from `mateEquiv_hcomp` and the
compatibility of mates with conjugates (`mateEquiv_conjugateEquiv_vcomp`,
`conjugateEquiv_mateEquiv_vcomp`).
-/

@[expose] public section

open CategoryTheory Functor TwoSquare

namespace CategoryTheory.Adjunction

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [Category* X₁] [Category* X₂] [Category* X₃]
  [Category* Y₁] [Category* Y₂] [Category* Y₃]
  {LXa : X₁ ⥤ X₂} {RXa : X₂ ⥤ X₁} (adjXa : LXa ⊣ RXa)
  {LXb : X₂ ⥤ X₃} {RXb : X₃ ⥤ X₂} (adjXb : LXb ⊣ RXb)
  {LXc : X₁ ⥤ X₃} {RXc : X₃ ⥤ X₁} (adjXc : LXc ⊣ RXc)
  {LYa : Y₁ ⥤ Y₂} {RYa : Y₂ ⥤ Y₁} (adjYa : LYa ⊣ RYa)
  {LYb : Y₂ ⥤ Y₃} {RYb : Y₃ ⥤ Y₂} (adjYb : LYb ⊣ RYb)
  {LYc : Y₁ ⥤ Y₃} {RYc : Y₃ ⥤ Y₁} (adjYc : LYc ⊣ RYc)
  {P₁ : X₁ ⥤ Y₁} {P₂ : X₂ ⥤ Y₂} {P₃ : X₃ ⥤ Y₃}
  (ea : P₂ ⋙ RYa ≅ RXa ⋙ P₁) (eb : P₃ ⋙ RYb ≅ RXb ⋙ P₂) (ec : P₃ ⋙ RYc ≅ RXc ⋙ P₁)
  (κX : RXb ⋙ RXa ≅ RXc) (κY : RYb ⋙ RYa ≅ RYc)

/-- **Composition of the mates `pushHomOfComapIso`.** If `e_c` is the composite of `e_a` and
`e_b` up to the composition isomorphisms `κ : R_b ⋙ R_a ≅ R_c` of the right adjoints, then the
mate of `e_c` is the composite of the mates of `e_a` and `e_b`, up to the conjugates
`θ : L_c ≅ L_a ⋙ L_b` of `κ`. -/
theorem pushHomOfComapIso_app_eq_comp
    (h : ∀ K, ec.hom.app K = κY.inv.app (P₃.obj K) ≫ RYa.map (eb.hom.app K) ≫
      ea.hom.app (RXb.obj K) ≫ P₁.map (κX.hom.app K)) (K : X₁) :
    (pushHomOfComapIso adjXc adjYc ec).app K =
      ((conjugateIsoEquiv (adjYa.comp adjYb) adjYc).symm κY).hom.app (P₁.obj K) ≫
        LYb.map ((pushHomOfComapIso adjXa adjYa ea).app K) ≫
        (pushHomOfComapIso adjXb adjYb eb).app (LXa.obj K) ≫
        P₃.map (((conjugateIsoEquiv (adjXa.comp adjXb) adjXc).symm κX).inv.app K) := by
  have key : (mateEquiv adjXc adjYc).symm (TwoSquare.mk _ _ _ _ ec.inv) =
      (((mateEquiv adjXa adjYa).symm (TwoSquare.mk _ _ _ _ ea.inv) ≫ᵥ
        (mateEquiv adjXb adjYb).symm (TwoSquare.mk _ _ _ _ eb.inv)).whiskerRight
          ((conjugateIsoEquiv (adjYa.comp adjYb) adjYc).symm κY).hom).whiskerLeft
        ((conjugateIsoEquiv (adjXa.comp adjXb) adjXc).symm κX).inv := by
    rw [Equiv.symm_apply_eq, conjugateEquiv_mateEquiv_vcomp adjXc (adjXa.comp adjXb) adjYc,
      mateEquiv_conjugateEquiv_vcomp (adjXa.comp adjXb) (adjYa.comp adjYb) adjYc,
      mateEquiv_hcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      conjugateIsoEquiv_symm_apply_hom, conjugateIsoEquiv_symm_apply_inv,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext K
    rw [← cancel_epi (ec.hom.app K), Iso.hom_inv_id_app, h]
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      TwoSquare.mk]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Functor.comp_obj]
    simp only [← P₁.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc, ← RYa.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj]
  have := NatTrans.congr_app key K
  simpa [pushHomOfComapIso] using this

end CategoryTheory.Adjunction
