/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd

/-!
# Morphism properties and binary products in over categories

If `C` has pullbacks, the binary product of `A` and `B` in `Over S` has as underlying object the
fibre product `A.left ×[S] B.left`. Hence, for a morphism `g : B ⟶ B'` in `Over S`, the underlying
morphism of `prod.map (𝟙 A) g` is a base change of `g.left`. We deduce that any morphism property
that is stable under base change is stable under taking the product with the identity of a fixed
object of `Over S`.

Along the same lines, the structure morphism of a finite product in `Over S` satisfies any
multiplicative morphism property that is stable under base change, as soon as the structure
morphisms of all factors do.

We also record that the intersection of two morphism properties which are stable under
colimits of shape `J` is again stable under colimits of shape `J`, and the analogous
statements for filtered colimits and for coproducts.
-/

@[expose] public section

universe w w' v u

open CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

section Inf

variable {C : Type u} [Category.{v} C] (P Q : MorphismProperty C)

instance isStableUnderColimitsOfShape_inf (J : Type*) [Category* J]
    [P.IsStableUnderColimitsOfShape J] [Q.IsStableUnderColimitsOfShape J] :
    (P ⊓ Q).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ :=
    ⟨IsStableUnderColimitsOfShape.condition X₁ X₂ c₁ c₂ h₁ h₂ f (fun j ↦ (hf j).1) φ hφ,
      IsStableUnderColimitsOfShape.condition X₁ X₂ c₁ c₂ h₁ h₂ f (fun j ↦ (hf j).2) φ hφ⟩

instance isStableUnderFilteredColimits_inf
    [IsStableUnderFilteredColimits.{w, w'} P] [IsStableUnderFilteredColimits.{w, w'} Q] :
    IsStableUnderFilteredColimits.{w, w'} (P ⊓ Q) where
  isStableUnderColimitsOfShape _ := inferInstance

instance isStableUnderCoproducts_inf
    [IsStableUnderCoproducts.{w} P] [IsStableUnderCoproducts.{w} Q] :
    IsStableUnderCoproducts.{w} (P ⊓ Q) where
  isStableUnderCoproductsOfShape _ := inferInstance

end Inf

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (P : MorphismProperty C)
  [P.IsStableUnderBaseChange] {S : C} {A B B' : Over S}

/-- The underlying morphism of `prod.map (𝟙 A) g` is, up to the canonical identification of the
binary product in `Over S` with the fibre product over `S`, the base change of `g.left` along
`pullback.snd A.hom B'.hom`. -/
lemma isPullback_pullbackMap_id (g : B ⟶ B') :
    IsPullback (pullback.snd A.hom B.hom)
      (pullback.map A.hom B.hom A.hom B'.hom (𝟙 A.left) g.left (𝟙 S) (by simp)
        (by simp [Over.w])) g.left (pullback.snd A.hom B'.hom) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback A.hom B'.hom).flip
  have : pullback.map A.hom B.hom A.hom B'.hom (𝟙 A.left) g.left (𝟙 S) (by simp)
      (by simp [Over.w]) ≫ pullback.fst A.hom B'.hom = pullback.fst A.hom B.hom := by simp
  rw [this, Over.w g]
  exact (IsPullback.of_hasPullback A.hom B.hom).flip

/-- Up to the canonical identification of binary products in `Over S` with fibre products over
`S`, the underlying morphism of `prod.map (𝟙 A) g` is `pullback.map`. -/
lemma prod_map_id_left_comp_prodLeftIsoPullback_hom (g : B ⟶ B') :
    (prod.map (𝟙 A) g).left ≫ (Over.prodLeftIsoPullback A B').hom =
      (Over.prodLeftIsoPullback A B).hom ≫
        pullback.map A.hom B.hom A.hom B'.hom (𝟙 A.left) g.left (𝟙 S) (by simp)
          (by simp [Over.w]) := by
  ext
  · simp [← Over.comp_left]
  · simp [← Over.comp_left]

/-- A morphism property stable under base change is stable under taking the product with the
identity in an over category: if `g : B ⟶ B'` in `Over S` satisfies `P g.left`, then
`P (prod.map (𝟙 A) g).left`. -/
theorem left_prod_map_id (g : B ⟶ B') (hg : P g.left) : P (prod.map (𝟙 A) g).left := by
  rw [← P.cancel_right_of_respectsIso _ (Over.prodLeftIsoPullback A B').hom,
    prod_map_id_left_comp_prodLeftIsoPullback_hom, P.cancel_left_of_respectsIso]
  exact P.of_isPullback (isPullback_pullbackMap_id g) hg

/-- A morphism property stable under base change is stable under taking the product with the
identity in an over category: if `g : B ⟶ B'` in `Over S` satisfies `P g.left`, then
`P (prod.map g (𝟙 A)).left`. -/
theorem left_prod_map_id' (g : B ⟶ B') (hg : P g.left) : P (prod.map g (𝟙 A)).left := by
  have h : prod.map g (𝟙 A) =
      (prod.braiding A B).inv ≫ prod.map (𝟙 A) g ≫ (prod.braiding A B').hom := by
    ext <;> simp
  have : IsIso ((prod.braiding A B).inv.left) :=
    inferInstanceAs (IsIso ((Over.forget S).map (prod.braiding A B).inv))
  have : IsIso ((prod.braiding A B').hom.left) :=
    inferInstanceAs (IsIso ((Over.forget S).map (prod.braiding A B').hom))
  rw [h, Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso,
    P.cancel_right_of_respectsIso]
  exact P.left_prod_map_id g hg


omit [HasPullbacks C] in
/-- Isomorphic objects of `Over S` have structure morphisms with the same properties. -/
lemma hom_of_iso (e : A ≅ B) (hB : P B.hom) : P A.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← Over.w e.hom, P.cancel_left_of_respectsIso]
  exact hB

variable [P.IsStableUnderComposition]

/-- The structure morphism of a binary product in `Over S` satisfies a multiplicative morphism
property that is stable under base change, as soon as the structure morphisms of both factors
do. -/
theorem left_prod_hom (A B : Over S) (hA : P A.hom) (hB : P B.hom) : P (A ⨯ B).hom := by
  have h : (Over.prodLeftIsoPullback A B).hom ≫ pullback.fst A.hom B.hom ≫ A.hom = (A ⨯ B).hom := by
    rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]
  rw [← h, P.cancel_left_of_respectsIso]
  exact P.comp_mem _ _ (P.of_isPullback (IsPullback.of_hasPullback A.hom B.hom).flip hB) hA

/-- The structure morphism of a finite product in `Over S` satisfies a multiplicative morphism
property that is stable under base change, as soon as the structure morphisms of all factors do. -/
theorem pi_hom [P.ContainsIdentities] [HasFiniteProducts (Over S)] {ι : Type*} [Finite ι]
    (F : ι → Over S) (hF : ∀ i, P (F i).hom) : P (∏ᶜ F).hom := by
  refine Finite.induction_empty_option
    (P := fun ι ↦ ∀ [Finite ι] (F : ι → Over S), (∀ i, P (F i).hom) → P (∏ᶜ F).hom)
    ?_ ?_ ?_ ι F hF
  · intro α β e hα _ F hF
    have : Finite α := Finite.of_equiv _ e.symm
    exact P.hom_of_iso (Pi.whiskerEquiv e fun j ↦ Iso.refl (F (e j))).symm
      (hα (fun j ↦ F (e j)) fun j ↦ hF (e j))
  · intro _ F _
    have hT : IsTerminal (∏ᶜ F) :=
      IsTerminal.ofUniqueHom (fun _ ↦ Pi.lift fun i ↦ i.elim)
        fun _ _ ↦ Pi.hom_ext _ _ fun i ↦ i.elim
    exact P.hom_of_iso (hT.uniqueUpToIso Over.mkIdTerminal) (by simpa using P.id_mem S)
  · intro α _ hα _ F hF
    exact P.hom_of_iso (piOptionIso F)
      (P.left_prod_hom _ _ (hF none) (hα _ fun i ↦ hF (some i)))

end CategoryTheory.MorphismProperty
