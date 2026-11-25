/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates and transported adjunctions commuting with shifts

* If two adjunctions commute with shifts, the mate of a natural transformation which
  commutes with shifts commutes with shifts (`NatTrans.CommShift.mateEquiv`). In particular, so
  does the conjugate of a natural transformation between left adjoints
  (`NatTrans.CommShift.conjugateEquiv`).
* An adjunction commuting with shifts, transported along an isomorphism of left adjoints
  commuting with shifts, commutes with shifts (`Adjunction.commShift_ofNatIsoLeft`).
-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {A : Type*} [AddMonoid A]

namespace NatTrans.CommShift

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [HasShift C A] [HasShift D A] [HasShift E A] [HasShift F A]
  {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
  [G.CommShift A] [H.CommShift A] [L₁.CommShift A] [R₁.CommShift A] [L₂.CommShift A]
  [R₂.CommShift A]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A] [adj₂.CommShift A]

/-- The mate of a natural transformation commuting with shifts, with respect to adjunctions
commuting with shifts, commutes with shifts. -/
lemma mateEquiv (α : TwoSquare G L₁ L₂ H) [NatTrans.CommShift α A] :
    NatTrans.CommShift (mateEquiv adj₁ adj₂ α) A := by
  dsimp only [CategoryTheory.mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk]
  infer_instance

end NatTrans.CommShift

namespace NatTrans.CommShift

variable {C D : Type*} [Category* C] [Category* D] [HasShift C A] [HasShift D A]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} [L₁.CommShift A] [L₂.CommShift A] [R₁.CommShift A]
  [R₂.CommShift A] (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A] [adj₂.CommShift A]

/-- The conjugate of a natural transformation commuting with shifts, with respect to
adjunctions commuting with shifts, commutes with shifts. It is the mate along identity
squares. -/
instance conjugateEquiv (α : L₂ ⟶ L₁) [NatTrans.CommShift α A] :
    NatTrans.CommShift (conjugateEquiv adj₁ adj₂ α) A := by
  have := mateEquiv (A := A) (G := 𝟭 C) (H := 𝟭 D) adj₁ adj₂
    (TwoSquare.mk _ _ _ _ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv))
  have e : CategoryTheory.conjugateEquiv adj₁ adj₂ α = R₁.rightUnitor.inv ≫
      (CategoryTheory.mateEquiv adj₁ adj₂
        (TwoSquare.mk _ _ _ _ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv))) ≫
      R₂.leftUnitor.hom := rfl
  rw [e]
  infer_instance

end NatTrans.CommShift

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] [HasShift C A] [HasShift D A]
  {F G : C ⥤ D} {H : D ⥤ C} [F.CommShift A] [G.CommShift A] [H.CommShift A]

/-- An adjunction commuting with shifts, transported along an isomorphism of left adjoints
commuting with shifts, commutes with shifts. -/
lemma commShift_ofNatIsoLeft (adj : F ⊣ H) (iso : F ≅ G) [adj.CommShift A]
    [NatTrans.CommShift iso.hom A] : (adj.ofNatIsoLeft iso).CommShift A where
  commShift_unit := by dsimp only [ofNatIsoLeft]; infer_instance
  commShift_counit := by dsimp only [ofNatIsoLeft]; infer_instance

end Adjunction

namespace NatTrans.CommShift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [HasShift C A] [HasShift D A]
  [HasShift E A] {L : C ⥤ D} {R : D ⥤ C} [L.CommShift A] [R.CommShift A] (adj : L ⊣ R)
  [adj.CommShift A] {F : E ⥤ C} {G : E ⥤ D} [F.CommShift A] [G.CommShift A]

/-- The transpose `F ⟶ G ⋙ R` along an adjunction `L ⊣ R` commuting with shifts of a natural
transformation `τ : F ⋙ L ⟶ G` commuting with shifts commutes with shifts. -/
lemma of_homEquiv (τ : F ⋙ L ⟶ G) [NatTrans.CommShift τ A] (σ : F ⟶ G ⋙ R)
    (h : ∀ X, σ.app X = adj.homEquiv _ _ (τ.app X)) : NatTrans.CommShift σ A := by
  have e : σ = (Functor.rightUnitor F).inv ≫ Functor.whiskerLeft F adj.unit ≫
      (Functor.associator F L R).inv ≫ Functor.whiskerRight τ R := by
    ext X
    simp [h X, Adjunction.homEquiv_unit]
  rw [e]
  infer_instance

end NatTrans.CommShift

end CategoryTheory
