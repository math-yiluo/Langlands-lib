/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveSystemData

/-! # Composition calculation at one outgoing-arrow factor

Source: Stacks Project, Tag 0EXZ, canonical product components.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private lemma transpose_iso {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (eL : L₂ ≅ L₁) (eR : R₁ ≅ R₂)
    (he : ∀ X, adj₂.unit.app X ≫ R₂.map (eL.hom.app X) =
      adj₁.unit.app X ≫ eR.hom.app (L₁.obj X))
    {X : C} {Y : D} (q : L₁.obj X ⟶ Y) :
    (adj₂.homEquiv _ _) (eL.hom.app X ≫ q) =
      (adj₁.homEquiv _ _) q ≫ eR.hom.app Y := by
  erw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, he,
    Category.assoc, ← eR.hom.naturality q, ← Category.assoc,
    ← Adjunction.homEquiv_unit]

private lemma component_transpose {C D E : Type*}
    [Category C] [Category D] [Category E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : C ⥤ E} {R₃ : E ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (eL : L₃ ≅ L₁ ⋙ L₂) (eR : R₂ ⋙ R₁ ≅ R₃)
    (he : ∀ X, adj₃.unit.app X ≫ R₃.map (eL.hom.app X) =
      (adj₁.comp adj₂).unit.app X ≫ eR.hom.app ((L₁ ⋙ L₂).obj X))
    {X : C} {B V : D} {Y : E}
    (a : L₁.obj X ⟶ B) (p : B ⟶ V) (q : X ⟶ R₁.obj V) (b : V ⟶ R₂.obj Y)
    (ha : a ≫ p = (adj₁.homEquiv _ _).symm q) :
    (adj₃.homEquiv _ _).symm (q ≫ R₁.map b ≫ eR.hom.app Y) =
      eL.hom.app X ≫ L₂.map a ≫ (adj₂.homEquiv _ _).symm (p ≫ b) := by
  apply (adj₃.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, transpose_iso (adj₁.comp adj₂) adj₃ eL eR he]
  rw [Adjunction.comp_homEquiv]
  change q ≫ R₁.map b ≫ eR.hom.app Y =
    adj₁.homEquiv _ _ (adj₂.homEquiv _ _
      (L₂.map a ≫ (adj₂.homEquiv _ _).symm (p ≫ b))) ≫ eR.hom.app Y
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  have hq : (adj₁.homEquiv _ _) (a ≫ p) = q := by
    rw [ha, Equiv.apply_symm_apply]
  rw [← Category.assoc a p b, Adjunction.homEquiv_naturality_right, hq, Category.assoc]

private lemma inverse_square {C : Type*} [Category C] {A B V W : C}
    (a : A ≅ B) (b : B ≅ W) (c : A ≅ V) (d : V ≅ W)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom) :
    d.inv = b.inv ≫ a.inv ≫ c.hom := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [← h]
  simp

private lemma inverse_associativity {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : ab = a ≫ b) (hbc : bc = b ≫ c) (habc : abc = ab ≫ c)
    (J : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (lowerStarComp AddCommGrpCat.{u + 1} a bc abc
      (by rw [habc, hab, hbc, Category.assoc])).inv.app J =
    (lowerStarComp AddCommGrpCat.{u + 1} ab c abc habc).inv.app J ≫
      (lowerStar AddCommGrpCat.{u + 1} c).map
        ((lowerStarComp AddCommGrpCat.{u + 1} a b ab hab).inv.app J) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} b c bc hbc).hom.app
        ((lowerStar AddCommGrpCat.{u + 1} a).obj J) := by
  have key := NatTrans.congr_app
    (lowerStarComp_assoc' AddCommGrpCat.{u + 1} a b c ab bc abc hab hbc habc) J
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  exact inverse_square
    ((lowerStar AddCommGrpCat.{u + 1} c).mapIso
      ((lowerStarComp AddCommGrpCat.{u + 1} a b ab hab).app J))
    ((lowerStarComp AddCommGrpCat.{u + 1} ab c abc habc).app J)
    ((lowerStarComp AddCommGrpCat.{u + 1} b c bc hbc).app
      ((lowerStar AddCommGrpCat.{u + 1} a).obj J))
    ((lowerStarComp AddCommGrpCat.{u + 1} a bc abc
      (by rw [habc, hab, hbc, Category.assoc])).app J) key

/-- Composition calculation at one outgoing-arrow factor.
Source: Stacks Project, Tag 0EXZ, canonical maps ψ, expanded with the adjunction
mate equations and direct-image coherence in UpperLowerStar.Coherence.
(blueprint: lem-weil-pbc-etale-coefficient-product-composition-component).

Proof: apply the injective homEquiv along D((f composed with g).op).
The unit mate equation upperStarComp_hom_app_unit_app and naturality of lowerStarComp
replace transposition after upperStarComp by two successive transpositions, followed
by lowerStarComp.hom at the target factor. Adjunction naturality in the source moves
the transition for f through the transpose for g. Naturality in the target moves
both inverse direct-image comparisons through the transpose for f. The projection
formula Pi.lift_comp_π removes the intervening product lift. The resulting expression
starts with the projection indexed by f composed with g composed with the outgoing
arrow. The inverse associativity equation obtained from lowerStarComp_assoc' equates
the two orders of inverse comparisons, and cancellation of lowerStarComp.hom with
its inverse leaves the left side. Category.assoc identifies the outgoing-arrow
indices; D.map_comp supplies the named scheme composites. This calculates one
factor only and does not assert an equality of maps into the whole product. -/
theorem etale_coefficient_product_composition_component
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (t : Σ l : I, k ⟶ l) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map (f ≫ g).op)).homEquiv _ _).symm
      (Pi.π (fun t : Σ l : I, i ⟶ l ↦
          (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
            (Injective.under (F t.1))) ⟨t.1, (f ≫ g) ≫ t.2⟩ ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (D.map t.2.op) (D.map (f ≫ g).op)
          (D.map ((f ≫ g) ≫ t.2).op) (D.map_comp t.2.op (f ≫ g).op)).inv.app
            (Injective.under (F t.1))) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
        (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app
          (etaleCoefficientInjectiveTarget D F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map
        (Pi.lift fun s : Σ l : I, j ⟶ l ↦
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op)).homEquiv _ _).symm
      (Pi.π (fun t : Σ l : I, i ⟶ l ↦
          (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
            (Injective.under (F t.1))) ⟨s.1, f ≫ s.2⟩ ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (D.map s.2.op) (D.map f.op)
          (D.map (f ≫ s.2).op) (D.map_comp s.2.op f.op)).inv.app
            (Injective.under (F s.1)))) ≫
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map g.op)).homEquiv _ _).symm
      (Pi.π (fun t : Σ l : I, j ⟶ l ↦
          (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
            (Injective.under (F t.1))) ⟨t.1, g ≫ t.2⟩ ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (D.map t.2.op) (D.map g.op)
          (D.map (g ≫ t.2).op) (D.map_comp t.2.op g.op)).inv.app
            (Injective.under (F t.1))) := by
  rcases t with ⟨l, h⟩
  let a := Pi.lift fun s : Σ l : I, j ⟶ l ↦
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op)).homEquiv _ _).symm
      (Pi.π (fun t : Σ l : I, i ⟶ l ↦
        (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
          (Injective.under (F t.1))) ⟨s.1, f ≫ s.2⟩ ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (D.map s.2.op) (D.map f.op)
          (D.map (f ≫ s.2).op) (D.map_comp s.2.op f.op)).inv.app
            (Injective.under (F s.1)))
  let p := Pi.π (fun t : Σ l : I, j ⟶ l ↦
    (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
      (Injective.under (F t.1))) ⟨l, g ≫ h⟩
  let q := Pi.π (fun t : Σ l : I, i ⟶ l ↦
    (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
      (Injective.under (F t.1))) ⟨l, f ≫ (g ≫ h)⟩ ≫
    (lowerStarComp AddCommGrpCat.{u + 1} (D.map (g ≫ h).op) (D.map f.op)
      (D.map (f ≫ (g ≫ h)).op) (D.map_comp (g ≫ h).op f.op)).inv.app
        (Injective.under (F l))
  let b := (lowerStarComp AddCommGrpCat.{u + 1} (D.map h.op) (D.map g.op)
    (D.map (g ≫ h).op) (D.map_comp h.op g.op)).inv.app (Injective.under (F l))
  have ha : a ≫ p =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op)).homEquiv _ _).symm
        q := by
    dsimp only [a, p, q]
    exact Pi.lift_comp_π _ (⟨l, g ≫ h⟩ : Σ l : I, j ⟶ l)
  have ht := component_transpose
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op))
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map g.op))
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map (f ≫ g).op))
    (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
      (D.map (f ≫ g).op) (D.map_comp g.op f.op))
    (lowerStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
      (D.map (f ≫ g).op) (D.map_comp g.op f.op))
    (fun X ↦ upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1}
      (D.map g.op) (D.map f.op) X (D.map (f ≫ g).op) (D.map_comp g.op f.op))
    a p q b ha
  have hi := inverse_associativity (D.map h.op) (D.map g.op) (D.map f.op)
    (D.map (g ≫ h).op) (D.map (f ≫ g).op) (D.map (f ≫ (g ≫ h)).op)
    (D.map_comp h.op g.op) (D.map_comp g.op f.op)
    (D.map_comp (g ≫ h).op f.op) (Injective.under (F l))
  have hp : Pi.π (fun t : Σ l : I, i ⟶ l ↦
      (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
        (Injective.under (F t.1))) ⟨l, (f ≫ g) ≫ h⟩ ≫
      (lowerStarComp AddCommGrpCat.{u + 1} (D.map h.op) (D.map (f ≫ g).op)
        (D.map ((f ≫ g) ≫ h).op) (D.map_comp h.op (f ≫ g).op)).inv.app
          (Injective.under (F l)) = q ≫
        (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map b ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app
            ((lowerStar AddCommGrpCat.{u + 1} (D.map h.op)).obj
              (Injective.under (F l))) := by
    dsimp only [q, b]
    have hassoc : (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h
    erw [hassoc, hi]
    simp only [Category.assoc]
  exact (congrArg
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (D.map (f ≫ g).op)).homEquiv _ _).symm hp).trans ht

end AlgebraicGeometry.Etale
