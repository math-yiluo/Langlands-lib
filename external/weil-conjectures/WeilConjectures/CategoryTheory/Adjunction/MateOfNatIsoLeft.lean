/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso

/-!
# Mates along a transported adjunction and along pasted squares

* `CategoryTheory.mateEquiv_ofNatIsoLeft`: the mate of a square under the adjunction
  `L₁' ⊣ R₁` transported along `e : L₁ ≅ L₁'` (`Adjunction.ofNatIsoLeft`) is the mate under
  `L₁ ⊣ R₁` of the square whiskered by `e⁻¹`.
* `CategoryTheory.isIso_mateEquiv_hComp`: the mate of the horizontal composite of two squares
  (pasted along the functors which are not adjoints) is invertible if both mates are.
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* E] [Category* F]

/-- The mate under an adjunction transported along an isomorphism of left adjoints
`e : L₁ ≅ L₁'` is the mate of the square whiskered by `e⁻¹`. -/
lemma mateEquiv_ofNatIsoLeft {G : A ⥤ C} {H : B ⥤ D} {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₁ ≅ L₁')
    (α : TwoSquare G L₁' L₂ H) :
    mateEquiv (adj₁.ofNatIsoLeft e) adj₂ α =
      mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ (α ≫ Functor.whiskerRight e.inv H)) := by
  ext X
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_counit]

/-- **Mates of pasted squares.** If the mates of `α : TwoSquare G₁ L₁ L₂ H₁` and
`β : TwoSquare G₂ L₂ L₃ H₂` are invertible, so is the mate of their composite
`α ≫ₕ β : TwoSquare (G₁ ⋙ G₂) L₁ L₃ (H₁ ⋙ H₂)`. -/
lemma isIso_mateEquiv_hComp {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (α : TwoSquare G₁ L₁ L₂ H₁)
    (β : TwoSquare G₂ L₂ L₃ H₂) [IsIso (mateEquiv adj₁ adj₂ α)]
    [IsIso (mateEquiv adj₂ adj₃ β)] :
    IsIso (mateEquiv adj₁ adj₃ (α ≫ₕ β)) := by
  rw [mateEquiv_vcomp adj₁ adj₂ adj₃]
  exact TwoSquare.isIso_vComp _ _

/-- **The mate of the commutation square of a restricted adjunction.** For an adjunction
`L' ⊣ R'` restricted along fully faithful functors `iC`, `iD` through
`comm1 : iC ⋙ L' ≅ L ⋙ iD` and `comm2 : iD ⋙ R' ≅ R ⋙ iC`
(`Adjunction.restrictFullyFaithful`), the mate of `comm1` is `comm2⁻¹`. -/
lemma mateEquiv_restrictFullyFaithful {iC : A ⥤ C} {iD : B ⥤ D} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L' ⊣ R') (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) {L : A ⥤ B} {R : B ⥤ A}
    (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC) :
    mateEquiv (adj.restrictFullyFaithful hiC hiD comm1 comm2) adj
      (TwoSquare.mk _ _ _ _ comm1.hom) = TwoSquare.mk _ _ _ _ comm2.inv := by
  ext Y
  have h := adj.unit.naturality (comm2.inv.app Y)
  have hc := adj.map_restrictFullyFaithful_counit_app hiC hiD comm1 comm2 Y
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h
  simp only [mateEquiv_apply, Functor.comp_obj, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id]
  rw [← R'.map_comp, hc, Iso.hom_inv_id_app_assoc, R'.map_comp, ← Category.assoc, ← h,
    Category.assoc, Adjunction.right_triangle_components, Category.comp_id]

end CategoryTheory
