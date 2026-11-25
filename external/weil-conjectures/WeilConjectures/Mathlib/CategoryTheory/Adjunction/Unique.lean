/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!

# The conjugate of the canonical isomorphism of two left adjoints

If `F` and `F'` are both left adjoint to `G`, the canonical isomorphism
`CategoryTheory.Adjunction.leftAdjointUniq` between them is, by construction, the
isomorphism conjugate to the identity of `G`. This file records that in the form used for
comparing mates: conjugating `Adjunction.leftAdjointUniq` in either direction gives the
identity of `G`.

## Main results

- `CategoryTheory.conjugateEquiv_leftAdjointUniq_hom` and
  `CategoryTheory.conjugateEquiv_leftAdjointUniq_inv`: the conjugates of the two
  directions of `Adjunction.leftAdjointUniq` are the identity of the common right adjoint.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {F F' : C ⥤ D} {G : D ⥤ C}

/-- The conjugate of `Adjunction.leftAdjointUniq adj₁ adj₂` is the identity of the common
right adjoint. -/
lemma conjugateEquiv_leftAdjointUniq_hom (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) :
    conjugateEquiv adj₂ adj₁ (Adjunction.leftAdjointUniq adj₁ adj₂).hom = 𝟙 G := by
  simp [Adjunction.leftAdjointUniq]

/-- The conjugate of the inverse of `Adjunction.leftAdjointUniq adj₁ adj₂` is the identity
of the common right adjoint. -/
lemma conjugateEquiv_leftAdjointUniq_inv (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) :
    conjugateEquiv adj₁ adj₂ (Adjunction.leftAdjointUniq adj₁ adj₂).inv = 𝟙 G := by
  simp [Adjunction.leftAdjointUniq]

section Mates

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}

/-- Mates are invariant under replacing the left adjoints by the canonically isomorphic
ones: if `w` is a 2-square

```
C ---G---> E
|          |
L₁'   ⇙    L₂'
v          v
D ---H---> F
```

and `L₁ ≅ L₁'`, `L₂ ≅ L₂'` are the isomorphisms `Adjunction.leftAdjointUniq` of left
adjoints of `R₁` resp. `R₂`, then the mate of `w` under `L₁' ⊣ R₁` and `L₂' ⊣ R₂` is the mate
of the transported 2-square `G ⋙ L₂ ⟶ G ⋙ L₂' ⟶ L₁' ⋙ H ⟶ L₁ ⋙ H` under `L₁ ⊣ R₁` and
`L₂ ⊣ R₂`. -/
lemma mateEquiv_leftAdjointUniq (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₂' : L₂' ⊣ R₂) (w : TwoSquare G L₁' L₂' H) :
    mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G (adj₂.leftAdjointUniq adj₂').hom ≫ w ≫
        Functor.whiskerRight (adj₁.leftAdjointUniq adj₁').inv H)) =
      mateEquiv adj₁' adj₂' w := by
  have h : TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G (adj₂.leftAdjointUniq adj₂').hom ≫ w ≫
        Functor.whiskerRight (adj₁.leftAdjointUniq adj₁').inv H) =
      (w.whiskerRight (adj₂.leftAdjointUniq adj₂').hom).whiskerLeft
        (adj₁.leftAdjointUniq adj₁').inv := by
    ext
    simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  rw [h, conjugateEquiv_mateEquiv_vcomp _ adj₁' _, mateEquiv_conjugateEquiv_vcomp _ adj₂' _,
    conjugateEquiv_leftAdjointUniq_inv, conjugateEquiv_leftAdjointUniq_hom]
  ext
  simp

end Mates

section RightAdjointUniq

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G G' : D ⥤ C}

/-- An isomorphism `e : G ≅ G'` between two right adjoints of `F` transports the first
adjunction to the second if and only if it is `Adjunction.rightAdjointUniq`. -/
lemma Adjunction.ofNatIsoRight_eq_iff (adj₁ : F ⊣ G) (adj₂ : F ⊣ G') (e : G ≅ G') :
    adj₁.ofNatIsoRight e = adj₂ ↔ e = adj₁.rightAdjointUniq adj₂ := by
  constructor
  · rintro rfl
    ext Y
    rw [← Equiv.apply_symm_apply ((adj₁.ofNatIsoRight e).homEquiv _ _)
      ((adj₁.rightAdjointUniq (adj₁.ofNatIsoRight e)).hom.app Y),
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app, Adjunction.homEquiv_ofNatIsoRight_apply]
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Category.id_comp]
  · rintro rfl
    apply Adjunction.ext
    ext X
    simp [Adjunction.ofNatIsoRight]

/-- If `G` and `G'` are both right adjoint to `F`, there is a unique isomorphism `G ≅ G'`
compatible with the two adjunctions, namely `Adjunction.rightAdjointUniq`. -/
lemma Adjunction.existsUnique_ofNatIsoRight_eq (adj₁ : F ⊣ G) (adj₂ : F ⊣ G') :
    ∃! e : G ≅ G', adj₁.ofNatIsoRight e = adj₂ :=
  ⟨_, (adj₁.ofNatIsoRight_eq_iff adj₂ _).2 rfl, fun _ h ↦ (adj₁.ofNatIsoRight_eq_iff adj₂ _).1 h⟩

end RightAdjointUniq

end CategoryTheory
