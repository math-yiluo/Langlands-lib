/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Abstract

/-!

# Projection morphisms are module structures

Let `F ⊣ G` be an adjunction between monoidal categories with `F` monoidal. The projection
morphism `G A ⊗ B ⟶ G (A ⊗ F B)` is compatible with the unit and the tensor structure of `F` in
its second variable (the axioms of a module functor). Dually the projection comparison
`P (M ⊗ S N) ⟶ P M ⊗ N` of an adjunction `P ⊣ S` with `S` lax monoidal satisfies the
corresponding axioms, hence so does its inverse when it is an isomorphism. The composite of such
a projection morphism, an inverse projection comparison and a monoidal identification
`Ff ≅ Fg ⋙ Fi` again satisfies the axioms; this is the shape of the exceptional projection
morphism `PF^!_f` of a compactification.

## Main statements

- `CategoryTheory.Adjunction.projectionMorphism_unit`,
  `CategoryTheory.Adjunction.projectionMorphism_tensor`: the axioms for the projection morphism.
- `CategoryTheory.Adjunction.inv_projectionComparison_unit`,
  `CategoryTheory.Adjunction.inv_projectionComparison_tensor`: the axioms for the inverse of the
  projection comparison.
- `CategoryTheory.Adjunction.projection_comp_unit`,
  `CategoryTheory.Adjunction.projection_comp_tensor`: the axioms for the composite.
- `CategoryTheory.NatIso.ε_comp_map_ε_comp_inv_app_of_eq_eqToIso_trans`,
  `CategoryTheory.NatIso.μ_comp_map_μ_comp_inv_app_of_eq_eqToIso_trans`: an identification
  `F a = F b ≅ G ⋙ H` compatible with the comonoidal structures is monoidal.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section ProjectionMorphism

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]

lemma projectionMorphism_unit (A : C) :
    adj.projectionMorphism A (𝟙_ D) = (ρ_ (G.obj A)).hom ≫ G.map ((ρ_ A).inv ≫ A ◁ ε F) := by
  rw [projectionMorphism, ← Equiv.eq_symm_apply, homEquiv_counit, F.map_comp, Category.assoc,
    counit_naturality, ← right_unitality_hom]
  simp only [Category.assoc]
  rw [← rightUnitor_naturality_assoc, Iso.hom_inv_id_assoc, whisker_exchange_assoc,
    ← whiskerLeft_comp, Functor.Monoidal.η_ε, whiskerLeft_id, Category.comp_id]

lemma projectionMorphism_tensor (A : C) (B B' : D) :
    adj.projectionMorphism A (B ⊗ B') = (α_ _ _ _).inv ≫ adj.projectionMorphism A B ▷ B' ≫
      adj.projectionMorphism (A ⊗ F.obj B) B' ≫ G.map ((α_ _ _ _).hom ≫ A ◁ μ F B B') := by
  have h : adj.projectionMorphism A B ▷ B' ≫ adj.projectionMorphism (A ⊗ F.obj B) B' =
      adj.homEquiv _ _ (δ F (G.obj A ⊗ B) B' ≫
        (δ F (G.obj A) B ≫ adj.counit.app A ▷ F.obj B) ▷ F.obj B') :=
    (adj.homEquiv_δ_whiskerRight _ B').symm
  rw [reassoc_of% h, projectionMorphism, ← homEquiv_naturality_right, ← homEquiv_naturality_left]
  congr 1
  simp only [Category.assoc, comp_whiskerRight]
  rw [associator_naturality_left_assoc, Functor.OplaxMonoidal.associativity_assoc,
    Iso.inv_hom_id_map_assoc, whisker_exchange_assoc, ← whiskerLeft_comp, Functor.Monoidal.δ_μ,
    whiskerLeft_id, Category.comp_id]

end ProjectionMorphism

section ProjectionComparison

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.LaxMonoidal]

lemma projectionComparison_unit (M : C) :
    P.map ((ρ_ M).inv ≫ M ◁ ε S) ≫ adj.projectionComparison M (𝟙_ D) = (ρ_ (P.obj M)).inv := by
  rw [projectionComparison, ← homEquiv_naturality_left_symm, Equiv.symm_apply_eq,
    homEquiv_unit, ← right_unitality_inv, Category.assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]
  rfl

lemma projectionComparison_tensor (M : C) (B B' : D) :
    P.map ((α_ _ _ _).hom ≫ M ◁ μ S B B') ≫ adj.projectionComparison M (B ⊗ B') =
      adj.projectionComparison (M ⊗ S.obj B) B' ≫ adj.projectionComparison M B ▷ B' ≫
        (α_ _ _ _).hom := by
  have hq : adj.homEquiv _ _ (adj.projectionComparison M B) =
      adj.unit.app M ▷ S.obj B ≫ μ S (P.obj M) B := by
    rw [projectionComparison, Equiv.apply_symm_apply]
  rw [homEquiv_unit] at hq
  rw [projectionComparison, projectionComparison, ← homEquiv_naturality_left_symm,
    ← homEquiv_naturality_right_symm]
  congr 1
  simp only [S.map_comp, Category.assoc]
  rw [← μ_natural_left_assoc, ← comp_whiskerRight_assoc, hq]
  simp only [comp_whiskerRight, Category.assoc]
  rw [Functor.LaxMonoidal.associativity]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [associator_naturality_left_assoc,
    ← whisker_exchange_assoc]

lemma inv_projectionComparison_unit (M : C) [IsIso (adj.projectionComparison M (𝟙_ D))] :
    inv (adj.projectionComparison M (𝟙_ D)) =
      (ρ_ (P.obj M)).hom ≫ P.map ((ρ_ M).inv ≫ M ◁ ε S) := by
  rw [← cancel_mono (adj.projectionComparison M (𝟙_ D)), IsIso.inv_hom_id, Category.assoc,
    projectionComparison_unit, Iso.hom_inv_id]

lemma inv_projectionComparison_tensor (M : C) (B B' : D)
    [IsIso (adj.projectionComparison M (B ⊗ B'))] [IsIso (adj.projectionComparison M B)]
    [IsIso (adj.projectionComparison (M ⊗ S.obj B) B')] :
    inv (adj.projectionComparison M (B ⊗ B')) =
      (α_ _ _ _).inv ≫ inv (adj.projectionComparison M B) ▷ B' ≫
        inv (adj.projectionComparison (M ⊗ S.obj B) B') ≫
          P.map ((α_ _ _ _).hom ≫ M ◁ μ S B B') := by
  rw [← cancel_mono (adj.projectionComparison M (B ⊗ B')), IsIso.inv_hom_id]
  simp only [Category.assoc]
  rw [projectionComparison_tensor, IsIso.inv_hom_id_assoc, ← comp_whiskerRight_assoc,
    IsIso.inv_hom_id, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

end ProjectionComparison

end CategoryTheory.Adjunction

namespace CategoryTheory.NatIso

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F₁ F₂ : C ⥤ D} [F₁.Monoidal] [F₂.Monoidal] (e : F₁ ≅ F₂)

lemma ε_comp_inv_app_of_hom_app_comp_η (h : e.hom.app (𝟙_ C) ≫ η F₂ = η F₁) :
    ε F₂ ≫ e.inv.app (𝟙_ C) = ε F₁ := by
  rw [← cancel_mono (η F₁), ← h, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.Monoidal.ε_η, h, Functor.Monoidal.ε_η]

lemma μ_comp_inv_app_of_δ_comp_tensorHom (X Y : C)
    (h : δ F₁ X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) = e.hom.app (X ⊗ Y) ≫ δ F₂ X Y) :
    μ F₂ X Y ≫ e.inv.app (X ⊗ Y) = (e.inv.app X ⊗ₘ e.inv.app Y) ≫ μ F₁ X Y := by
  have h' : e.inv.app (X ⊗ Y) ≫ δ F₁ X Y = δ F₂ X Y ≫ (e.inv.app X ⊗ₘ e.inv.app Y) := by
    rw [← cancel_epi (e.hom.app (X ⊗ Y)), Iso.hom_inv_id_app_assoc, ← reassoc_of% h,
      tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app, id_tensorHom_id,
      Category.comp_id]
  rw [← cancel_mono (δ F₁ X Y), Category.assoc, h', Functor.Monoidal.μ_δ_assoc, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

section EqToIso

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E] {α : Sort*} {F : α → C ⥤ E} [∀ a, (F a).Monoidal]
  {G : C ⥤ D} {H : D ⥤ E} [G.Monoidal] [H.Monoidal] {a b : α} (e : F b ≅ G ⋙ H)

/-- For a family `F` of monoidal functors, an equality `a = b` and a natural isomorphism
`e : F b ≅ G ⋙ H` compatible with the counits (given by `ηG`, `ηH` and `ηF`), the inverse of
`e' = (F a = F b ≅ G ⋙ H)` is compatible with the units. -/
lemma ε_comp_map_ε_comp_inv_app_of_eq_eqToIso_trans (h : a = b) (p : F a = F b)
    (e' : F a ≅ G ⋙ H) (hp : e' = eqToIso p ≪≫ e) {ηG : G.obj (𝟙_ C) ⟶ 𝟙_ D}
    {ηH : H.obj (𝟙_ D) ⟶ 𝟙_ E} {ηF : (F b).obj (𝟙_ C) ⟶ 𝟙_ E} (hG : η G = ηG) (hH : η H = ηH)
    (hF : η (F b) = ηF) (he : e.hom.app (𝟙_ C) ≫ H.map ηG ≫ ηH = ηF) :
    ε H ≫ H.map (ε G) ≫ e'.inv.app (𝟙_ C) = ε (F a) := by
  subst hp h hG hH hF
  rw [eqToIso_refl, Iso.refl_trans]
  have := ε_comp_inv_app_of_hom_app_comp_η e (by simpa using he)
  simpa using this

/-- For a family `F` of monoidal functors, an equality `a = b` and a natural isomorphism
`e : F b ≅ G ⋙ H` compatible with the comultiplications, the inverse of
`e' = (F a = F b ≅ G ⋙ H)` is compatible with the multiplications. -/
lemma μ_comp_map_μ_comp_inv_app_of_eq_eqToIso_trans (h : a = b) (p : F a = F b)
    (e' : F a ≅ G ⋙ H) (hp : e' = eqToIso p ≪≫ e) (X Y : C)
    (he : δ (F b) X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) = e.hom.app (X ⊗ Y) ≫ δ (G ⋙ H) X Y) :
    μ H (G.obj X) (G.obj Y) ≫ H.map (μ G X Y) ≫ e'.inv.app (X ⊗ Y) =
      (e'.inv.app X ⊗ₘ e'.inv.app Y) ≫ μ (F a) X Y := by
  subst hp h
  rw [eqToIso_refl, Iso.refl_trans]
  have := μ_comp_inv_app_of_δ_comp_tensorHom e X Y he
  simpa using this

end EqToIso

end CategoryTheory.NatIso

namespace CategoryTheory.Adjunction

section Composite

variable {𝒰 𝒵 𝒴 : Type*} [Category* 𝒰] [Category* 𝒵] [Category* 𝒴] [MonoidalCategory 𝒰]
  [MonoidalCategory 𝒵] [MonoidalCategory 𝒴] (I : 𝒰 ⥤ 𝒵) (G : 𝒵 ⥤ 𝒴) {Fg : 𝒴 ⥤ 𝒵}
  {Fi : 𝒵 ⥤ 𝒰} {Ff : 𝒴 ⥤ 𝒰} [Fg.LaxMonoidal] [Fi.LaxMonoidal] [Ff.LaxMonoidal]
  (e : Ff ≅ Fg ⋙ Fi) (pm : ∀ (A : 𝒵) (B : 𝒴), G.obj A ⊗ B ⟶ G.obj (A ⊗ Fg.obj B))
  (iq : ∀ (K : 𝒰) (N : 𝒵), I.obj K ⊗ N ⟶ I.obj (K ⊗ Fi.obj N))

lemma projection_comp_unit
    (hpm : ∀ A, pm A (𝟙_ 𝒴) = (ρ_ (G.obj A)).hom ≫ G.map ((ρ_ A).inv ≫ A ◁ ε Fg))
    (hiq : ∀ K, iq K (𝟙_ 𝒵) = (ρ_ (I.obj K)).hom ≫ I.map ((ρ_ K).inv ≫ K ◁ ε Fi))
    (hiq_right : ∀ (K : 𝒰) {N N' : 𝒵} (h : N ⟶ N'),
      I.obj K ◁ h ≫ iq K N' = iq K N ≫ I.map (K ◁ Fi.map h))
    (he : ε Fi ≫ Fi.map (ε Fg) ≫ e.inv.app (𝟙_ 𝒴) = ε Ff) (K : 𝒰) :
    pm (I.obj K) (𝟙_ 𝒴) ≫ G.map (iq K (Fg.obj (𝟙_ 𝒴)) ≫ I.map (K ◁ e.inv.app (𝟙_ 𝒴))) =
      (ρ_ (G.obj (I.obj K))).hom ≫ G.map (I.map ((ρ_ K).inv ≫ K ◁ ε Ff)) := by
  rw [hpm, Category.assoc, ← G.map_comp, Category.assoc, reassoc_of% (hiq_right K (ε Fg)), hiq,
    ← he]
  simp

lemma projection_comp_tensor
    (hpm : ∀ A B C, pm A (B ⊗ C) = (α_ _ _ _).inv ≫ pm A B ▷ C ≫
      pm (A ⊗ Fg.obj B) C ≫ G.map ((α_ _ _ _).hom ≫ A ◁ μ Fg B C))
    (hpm_left : ∀ {A A' : 𝒵} (φ : A ⟶ A') (B : 𝒴),
      G.map φ ▷ B ≫ pm A' B = pm A B ≫ G.map (φ ▷ Fg.obj B))
    (hiq : ∀ K B C, iq K (B ⊗ C) = (α_ _ _ _).inv ≫ iq K B ▷ C ≫
      iq (K ⊗ Fi.obj B) C ≫ I.map ((α_ _ _ _).hom ≫ K ◁ μ Fi B C))
    (hiq_left : ∀ {K K' : 𝒰} (φ : K ⟶ K') (N : 𝒵),
      I.map φ ▷ N ≫ iq K' N = iq K N ≫ I.map (φ ▷ Fi.obj N))
    (hiq_right : ∀ (K : 𝒰) {N N' : 𝒵} (h : N ⟶ N'),
      I.obj K ◁ h ≫ iq K N' = iq K N ≫ I.map (K ◁ Fi.map h))
    (he : ∀ B C, μ Fi (Fg.obj B) (Fg.obj C) ≫ Fi.map (μ Fg B C) ≫ e.inv.app (B ⊗ C) =
      (e.inv.app B ⊗ₘ e.inv.app C) ≫ μ Ff B C) (K : 𝒰) (B C : 𝒴) :
    pm (I.obj K) (B ⊗ C) ≫ G.map (iq K (Fg.obj (B ⊗ C)) ≫ I.map (K ◁ e.inv.app (B ⊗ C))) =
      (α_ _ _ _).inv ≫
        (pm (I.obj K) B ≫ G.map (iq K (Fg.obj B) ≫ I.map (K ◁ e.inv.app B))) ▷ C ≫
        (pm (I.obj (K ⊗ Ff.obj B)) C ≫
          G.map (iq (K ⊗ Ff.obj B) (Fg.obj C) ≫ I.map ((K ⊗ Ff.obj B) ◁ e.inv.app C))) ≫
        G.map (I.map ((α_ _ _ _).hom ≫ K ◁ μ Ff B C)) := by
  rw [hpm]
  simp only [comp_whiskerRight, Category.assoc]
  rw [reassoc_of% (hpm_left _ C)]
  simp only [← G.map_comp, Category.assoc]
  refine congrArg (fun x ↦ _ ≫ _ ≫ _ ≫ G.map x) ?_
  rw [reassoc_of% (hiq_right K (μ Fg B C)), hiq, Category.assoc, Iso.hom_inv_id_assoc,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [reassoc_of% (hiq_left (K ◁ e.inv.app B) (Fg.obj C))]
  simp only [Category.assoc, ← I.map_comp]
  refine congrArg (fun x ↦ _ ≫ _ ≫ I.map x) ?_
  simp only [← whiskerLeft_comp, he B C]
  rw [associator_naturality_right_assoc, associator_naturality_middle_assoc, ← whiskerLeft_comp,
    ← whiskerLeft_comp, ← tensorHom_def_assoc]

end Composite

end CategoryTheory.Adjunction
