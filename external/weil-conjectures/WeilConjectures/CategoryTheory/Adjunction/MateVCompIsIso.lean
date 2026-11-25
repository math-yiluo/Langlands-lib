/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Invertible mates of stacked squares

Consider two squares of functors stacked along their adjoint sides,
```
      L₁        L₃
   A ---→ B ---→ C
 G ↓  α   ↓ H  β ↓ K
   D ---→ E ---→ F
      L₂        L₄
```
with adjunctions `Lᵢ ⊣ Rᵢ`. If the mates of `α` and `β` are invertible, then so is the mate of
the composite square, even after replacing the composite left adjoints `L₁ ⋙ L₃` and `L₂ ⋙ L₄`
by isomorphic functors `L ≅ L₁ ⋙ L₃` and `L' ≅ L₂ ⋙ L₄` with arbitrary adjunctions `L ⊣ R` and
`L' ⊣ R'` (`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`).

This is the formal part of the compatibility of a coefficient comparison for exceptional
inverse images with composition (`Rf_! ⋙ Rg_! ≅ R(f ≫ g)_!`).
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* E] [Category* F]

/-- Whiskering an invertible square with an isomorphism of its top functor gives an invertible
square. -/
lemma TwoSquare.isIso_whiskerTop {T T' : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D}
    (w : TwoSquare T' L R Bo) (α : T ⟶ T') [IsIso w] [IsIso α] :
    IsIso (w.whiskerTop α) :=
  inferInstanceAs (IsIso (Functor.whiskerRight α R ≫ w))

/-- Whiskering an invertible square with an isomorphism of its bottom functor gives an
invertible square. -/
lemma TwoSquare.isIso_whiskerBottom {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo Bo' : C ⥤ D}
    (w : TwoSquare T L R Bo) (α : Bo ⟶ Bo') [IsIso w] [IsIso α] :
    IsIso (w.whiskerBottom α) :=
  inferInstanceAs (IsIso (w ≫ Functor.whiskerLeft L α))

/-- The horizontal composite of invertible squares is invertible. -/
lemma TwoSquare.isIso_hComp {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D} {T' : B ⥤ E}
    {R' : E ⥤ F} {Bo' : D ⥤ F} (w : TwoSquare T L R Bo) (w' : TwoSquare T' R R' Bo')
    [IsIso w] [IsIso w'] : IsIso (w ≫ₕ w') :=
  inferInstanceAs (IsIso ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft T w' ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight w Bo' ≫
    (Functor.associator _ _ _).hom))

/-- Whiskering an invertible square with an isomorphism of its left functor gives an invertible
square. -/
lemma TwoSquare.isIso_whiskerLeft {T : A ⥤ B} {L L' : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D}
    (w : TwoSquare T L R Bo) (α : L ⟶ L') [IsIso w] [IsIso α] :
    IsIso (w.whiskerLeft α) :=
  inferInstanceAs (IsIso (w ≫ Functor.whiskerRight α Bo))

/-- Whiskering an invertible square with an isomorphism of its right functor gives an
invertible square. -/
lemma TwoSquare.isIso_whiskerRight {T : A ⥤ B} {L : A ⥤ C} {R R' : B ⥤ D} {Bo : C ⥤ D}
    (w : TwoSquare T L R' Bo) (α : R ⟶ R') [IsIso w] [IsIso α] :
    IsIso (w.whiskerRight α) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft T α ≫ w))

/-- The vertical composite of invertible squares is invertible. -/
lemma TwoSquare.isIso_vComp {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D} {L' : C ⥤ E}
    {R' : D ⥤ F} {Bo' : E ⥤ F} (w : TwoSquare T L R Bo) (w' : TwoSquare Bo L' R' Bo')
    [IsIso w] [IsIso w'] : IsIso (w ≫ᵥ w') :=
  inferInstanceAs (IsIso ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight w R' ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L w' ≫
    (Functor.associator _ _ _).inv))

/-- **The mate of a stack of squares with invertible mates is invertible.** Let
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` and `β : H ⋙ L₄ ⟶ L₃ ⋙ K` be squares whose mates under `L₁ ⊣ R₁`,
`L₂ ⊣ R₂`, resp. `L₃ ⊣ R₃`, `L₄ ⊣ R₄` are invertible. For isomorphisms `e : L ≅ L₁ ⋙ L₃`,
`e' : L' ≅ L₂ ⋙ L₄` and adjunctions `L ⊣ R`, `L' ⊣ R'`, the mate of the stacked square
`G ⋙ L' ≅ G ⋙ L₂ ⋙ L₄ ⟶ L₁ ⋙ L₃ ⋙ K ≅ L ⋙ K` is invertible. -/
theorem isIso_mateEquiv_vComp_whiskerLeft_whiskerRight {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D} {L₃ : B ⥤ C} {R₃ : C ⥤ B}
    {L₄ : E ⥤ F} {R₄ : F ⥤ E} {L : A ⥤ C} {R : C ⥤ A} {L' : D ⥤ F} {R' : F ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄) (adj : L ⊣ R)
    (adj' : L' ⊣ R') (e : L ≅ L₁ ⋙ L₃) (e' : L' ≅ L₂ ⋙ L₄) (α : TwoSquare G L₁ L₂ H)
    (β : TwoSquare H L₃ L₄ K) [IsIso (mateEquiv adj₁ adj₂ α)]
    [IsIso (mateEquiv adj₃ adj₄ β)] :
    IsIso (mateEquiv adj adj' (((α ≫ᵥ β).whiskerLeft e.inv).whiskerRight e'.hom)) := by
  rw [mateEquiv_conjugateEquiv_vcomp adj (adj₂.comp adj₄) adj',
    conjugateEquiv_mateEquiv_vcomp adj (adj₁.comp adj₃) (adj₂.comp adj₄), mateEquiv_hcomp]
  have := (mateEquiv adj₃ adj₄ β).isIso_hComp (mateEquiv adj₁ adj₂ α)
  have := TwoSquare.isIso_whiskerTop (mateEquiv adj₃ adj₄ β ≫ₕ mateEquiv adj₁ adj₂ α)
    (conjugateEquiv adj (adj₁.comp adj₃) e.inv)
  exact TwoSquare.isIso_whiskerBottom _ (conjugateEquiv (adj₂.comp adj₄) adj' e'.hom)

end CategoryTheory
