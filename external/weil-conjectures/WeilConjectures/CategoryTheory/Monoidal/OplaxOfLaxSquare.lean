/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Oplax monoidal structures induced through lax monoidal functors

Consider a square of functors between monoidal categories
```
  K₁ ──F──▶ K₂
  │         │
  Q₁        Q₂
  ▼         ▼
  D₁ ──G──▶ D₂
```
with `Q₁` and `Q₂` lax monoidal, `F` oplax monoidal, and a natural isomorphism
`e : Q₁ ⋙ G ⟶ F ⋙ Q₂`. Let `δG : G(X ⊗ Y) ⟶ G X ⊗ G Y` be a natural transformation which is
compatible with the comonoidal structure of `F` on objects coming from `K₁`, in the sense that
```
  G(Q₁ a ⊗ Q₁ b) ──δG──▶ G(Q₁ a) ⊗ G(Q₁ b) ──e ⊗ e──▶ Q₂(F a) ⊗ Q₂(F b) ──μ──▶ Q₂(F a ⊗ F b)
```
agrees with `G(μ) ≫ e ≫ Q₂(δ F)`. Suppose moreover that every object of `D₁` is isomorphic to
`Q₁ a` for an `a` in a class `S` of objects such that `μ Q₂ x (F b)` is an isomorphism for all
`x` and all `b` in `S`. Then `δG`, together with the unit induced by `F`, is an oplax monoidal
structure on `G` (`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare`). It suffices that the
components `e a` for `a` in `S` are isomorphisms
(`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare'`).

The typical example is that of a functor `G` between derived categories induced by a monoidal
functor `F` between homotopy categories, `Q₁` and `Q₂` being the localization functors, and `S`
a class of K-flat complexes.
-/

@[expose] public section

namespace CategoryTheory.Functor.OplaxMonoidal

open Category MonoidalCategory LaxMonoidal

variable {K₁ K₂ D₁ D₂ : Type*} [Category* K₁] [Category* K₂] [Category* D₁] [Category* D₂]
  [MonoidalCategory K₁] [MonoidalCategory K₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  {G : D₁ ⥤ D₂}
  (δG : (postcompose₂.obj G).obj (curriedTensor D₁) ⟶
    (((whiskeringLeft₂ D₂).obj G).obj G).obj (curriedTensor D₂))

section

variable {X X' : D₁} (Y : D₁) (f : X ⟶ X')

@[reassoc]
lemma app_app_comp_whiskerRight :
    (δG.app X).app Y ≫ G.map f ▷ G.obj Y = G.map (f ▷ Y) ≫ (δG.app X').app Y :=
  (congr_app (δG.naturality f) Y).symm

@[reassoc]
lemma app_app_comp_whiskerLeft :
    (δG.app Y).app X ≫ G.obj Y ◁ G.map f = G.map (Y ◁ f) ≫ (δG.app Y).app X' :=
  ((δG.app Y).naturality f).symm

variable {Y Y' : D₁} (g : Y ⟶ Y')

@[reassoc]
lemma app_app_comp_tensorHom :
    (δG.app X).app Y ≫ (G.map f ⊗ₘ G.map g) = G.map (f ⊗ₘ g) ≫ (δG.app X').app Y' := by
  rw [tensorHom_def, tensorHom_def, app_app_comp_whiskerRight_assoc, app_app_comp_whiskerLeft,
    G.map_comp, assoc]

end

/-- The associativity axiom of an oplax monoidal structure with comonoidal structure `δG` holds
for `X, Y, Z` as soon as it holds for objects `X', Y', Z'` isomorphic to them. -/
lemma oplax_associativity_of_iso {X Y Z X' Y' Z' : D₁} (iX : X' ≅ X) (iY : Y' ≅ Y) (iZ : Z' ≅ Z)
    (h : (δG.app (X' ⊗ Y')).app Z' ≫ (δG.app X').app Y' ▷ G.obj Z' ≫
        (α_ (G.obj X') (G.obj Y') (G.obj Z')).hom =
      G.map (α_ X' Y' Z').hom ≫ (δG.app X').app (Y' ⊗ Z') ≫
        G.obj X' ◁ (δG.app Y').app Z') :
    (δG.app (X ⊗ Y)).app Z ≫ (δG.app X).app Y ▷ G.obj Z ≫
        (α_ (G.obj X) (G.obj Y) (G.obj Z)).hom =
      G.map (α_ X Y Z).hom ≫ (δG.app X).app (Y ⊗ Z) ≫ G.obj X ◁ (δG.app Y).app Z := by
  rw [← cancel_epi (G.map ((iX.hom ⊗ₘ iY.hom) ⊗ₘ iZ.hom))]
  have l : G.map ((iX.hom ⊗ₘ iY.hom) ⊗ₘ iZ.hom) ≫ (δG.app (X ⊗ Y)).app Z ≫
      (δG.app X).app Y ▷ G.obj Z ≫ (α_ (G.obj X) (G.obj Y) (G.obj Z)).hom =
      ((δG.app (X' ⊗ Y')).app Z' ≫ (δG.app X').app Y' ▷ G.obj Z' ≫
        (α_ (G.obj X') (G.obj Y') (G.obj Z')).hom) ≫
        (G.map iX.hom ⊗ₘ (G.map iY.hom ⊗ₘ G.map iZ.hom)) := by
    rw [← app_app_comp_tensorHom_assoc, tensorHom_comp_whiskerRight_assoc,
      ← app_app_comp_tensorHom, ← whiskerRight_comp_tensorHom_assoc, associator_naturality]
    simp only [assoc]
  have r : G.map ((iX.hom ⊗ₘ iY.hom) ⊗ₘ iZ.hom) ≫ G.map (α_ X Y Z).hom ≫
      (δG.app X).app (Y ⊗ Z) ≫ G.obj X ◁ (δG.app Y).app Z =
      (G.map (α_ X' Y' Z').hom ≫ (δG.app X').app (Y' ⊗ Z') ≫
        G.obj X' ◁ (δG.app Y').app Z') ≫
        (G.map iX.hom ⊗ₘ (G.map iY.hom ⊗ₘ G.map iZ.hom)) := by
    rw [← G.map_comp_assoc, associator_naturality, G.map_comp_assoc,
      ← app_app_comp_tensorHom_assoc, tensorHom_comp_whiskerLeft, ← app_app_comp_tensorHom,
      ← whiskerLeft_comp_tensorHom]
    simp only [assoc]
  rw [l, r, h]

lemma _root_.CategoryTheory.MonoidalCategory.comp_tensorHom_comp_comp {C : Type*} [Category* C]
    [MonoidalCategory C] {A B B' B'' X Y : C} (f : A ⟶ B) (g : B ⟶ B') (h : B' ⟶ B'')
    (k : X ⟶ Y) :
    (f ≫ g ≫ h) ⊗ₘ k = f ▷ X ≫ (g ⊗ₘ k) ≫ h ▷ Y := by
  simp [tensorHom_def, whisker_exchange]

lemma _root_.CategoryTheory.MonoidalCategory.tensorHom_comp_comp_comp {C : Type*} [Category* C]
    [MonoidalCategory C] {A B B' B'' X Y : C} (f : A ⟶ B) (g : B ⟶ B') (h : B' ⟶ B'')
    (k : X ⟶ Y) :
    k ⊗ₘ (f ≫ g ≫ h) = X ◁ f ≫ (k ⊗ₘ g) ≫ Y ◁ h := by
  rw [tensorHom_def, tensorHom_def, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [assoc]
  rw [whisker_exchange_assoc]

variable {ηG : G.obj (𝟙_ D₁) ⟶ 𝟙_ D₂}

/-- The left unitality axiom of an oplax monoidal structure holds for `X` as soon as it holds
for an object `X'` isomorphic to `X`. -/
lemma oplax_left_unitality_of_iso {X X' : D₁} (iX : X' ≅ X)
    (h : (λ_ (G.obj X')).inv = G.map (λ_ X').inv ≫ (δG.app (𝟙_ D₁)).app X' ≫ ηG ▷ G.obj X') :
    (λ_ (G.obj X)).inv = G.map (λ_ X).inv ≫ (δG.app (𝟙_ D₁)).app X ≫ ηG ▷ G.obj X := by
  rw [← cancel_epi (G.map iX.hom), leftUnitor_inv_naturality, ← G.map_comp_assoc,
    leftUnitor_inv_naturality, G.map_comp_assoc, ← app_app_comp_whiskerLeft_assoc,
    whisker_exchange, h]
  simp only [assoc]

/-- The right unitality axiom of an oplax monoidal structure holds for `X` as soon as it holds
for an object `X'` isomorphic to `X`. -/
lemma oplax_right_unitality_of_iso {X X' : D₁} (iX : X' ≅ X)
    (h : (ρ_ (G.obj X')).inv = G.map (ρ_ X').inv ≫ (δG.app X').app (𝟙_ D₁) ≫ G.obj X' ◁ ηG) :
    (ρ_ (G.obj X)).inv = G.map (ρ_ X).inv ≫ (δG.app X).app (𝟙_ D₁) ≫ G.obj X ◁ ηG := by
  rw [← cancel_epi (G.map iX.hom), rightUnitor_inv_naturality, ← G.map_comp_assoc,
    rightUnitor_inv_naturality, G.map_comp_assoc, ← app_app_comp_whiskerRight_assoc,
    ← whisker_exchange, h]
  simp only [assoc]

variable {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
  {F : K₁ ⥤ K₂} [F.OplaxMonoidal] (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a))
  (he : ∀ ⦃a b : K₁⦄ (f : a ⟶ b), G.map (Q₁.map f) ≫ e b = e a ≫ Q₂.map (F.map f))
  (hδ : ∀ a b, (δG.app (Q₁.obj a)).app (Q₁.obj b) ≫ (e a ⊗ₘ e b) ≫
    μ Q₂ (F.obj a) (F.obj b) = G.map (μ Q₁ a b) ≫ e (a ⊗ b) ≫ Q₂.map (δ F a b))

include hδ he in
/-- The associativity axiom holds for objects of the form `Q₁ a`, `Q₁ b`, `Q₁ c`, provided the
relevant components of `μ Q₂` and `e` are isomorphisms. -/
lemma oplax_associativity_of_lax_square (a b c : K₁) [IsIso (e a)] [IsIso (e b)] [IsIso (e c)]
    [IsIso (μ Q₂ (F.obj a) (F.obj b))] [IsIso (μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c))] :
    (δG.app (Q₁.obj a ⊗ Q₁.obj b)).app (Q₁.obj c) ≫
        (δG.app (Q₁.obj a)).app (Q₁.obj b) ▷ G.obj (Q₁.obj c) ≫
          (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).hom =
      G.map (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom ≫
        (δG.app (Q₁.obj a)).app (Q₁.obj b ⊗ Q₁.obj c) ≫
          G.obj (Q₁.obj a) ◁ (δG.app (Q₁.obj b)).app (Q₁.obj c) := by
  rw [← cancel_mono ((α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).inv ≫
    ((e a ⊗ₘ e b) ⊗ₘ e c) ≫
    μ Q₂ (F.obj a) (F.obj b) ▷ Q₂.obj (F.obj c) ≫ μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c))]
  have l : ((δG.app (Q₁.obj a ⊗ Q₁.obj b)).app (Q₁.obj c) ≫
      (δG.app (Q₁.obj a)).app (Q₁.obj b) ▷ G.obj (Q₁.obj c) ≫
        (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).hom) ≫
      (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).inv ≫
        ((e a ⊗ₘ e b) ⊗ₘ e c) ≫
        μ Q₂ (F.obj a) (F.obj b) ▷ Q₂.obj (F.obj c) ≫ μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c) =
      G.map (μ Q₁ a b ▷ Q₁.obj c) ≫ G.map (μ Q₁ (a ⊗ b) c) ≫ e ((a ⊗ b) ⊗ c) ≫
        Q₂.map (δ F (a ⊗ b) c) ≫ Q₂.map (δ F a b ▷ F.obj c) := by
    simp only [assoc, Iso.hom_inv_id_assoc]
    rw [whiskerRight_comp_tensorHom_assoc, tensorHom_comp_whiskerRight_assoc,
      assoc ((δG.app (Q₁.obj a)).app (Q₁.obj b)),
      hδ, comp_tensorHom_comp_comp]
    simp only [assoc]
    rw [μ_natural_left, app_app_comp_whiskerRight_assoc, reassoc_of% hδ]
  have r : (G.map (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom ≫
      (δG.app (Q₁.obj a)).app (Q₁.obj b ⊗ Q₁.obj c) ≫
        G.obj (Q₁.obj a) ◁ (δG.app (Q₁.obj b)).app (Q₁.obj c)) ≫
      (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).inv ≫
        ((e a ⊗ₘ e b) ⊗ₘ e c) ≫
        μ Q₂ (F.obj a) (F.obj b) ▷ Q₂.obj (F.obj c) ≫ μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c) =
      G.map (μ Q₁ a b ▷ Q₁.obj c) ≫ G.map (μ Q₁ (a ⊗ b) c) ≫ e ((a ⊗ b) ⊗ c) ≫
        Q₂.map (δ F (a ⊗ b) c) ≫ Q₂.map (δ F a b ▷ F.obj c) := by
    simp only [assoc]
    rw [← associator_inv_naturality_assoc, ← LaxMonoidal.associativity_inv,
      whiskerLeft_comp_tensorHom_assoc, tensorHom_comp_whiskerLeft_assoc,
      assoc ((δG.app (Q₁.obj b)).app (Q₁.obj c)), hδ, tensorHom_comp_comp_comp]
    simp only [assoc]
    rw [μ_natural_right_assoc, app_app_comp_whiskerLeft_assoc, reassoc_of% hδ,
      ← G.map_comp_assoc, ← G.map_comp_assoc,
      Category.assoc (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom, ← LaxMonoidal.associativity,
      G.map_comp_assoc,
      G.map_comp_assoc]
    rw [reassoc_of% (he (α_ a b c).hom), ← Q₂.map_comp, ← Q₂.map_comp, ← Q₂.map_comp,
      OplaxMonoidal.associativity_inv, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, id_comp,
      Q₂.map_comp]
  rw [l, r]

include hδ he in
/-- The left unitality axiom holds for an object of the form `Q₁ a`, provided the relevant
components of `μ Q₂` and `e` are isomorphisms. -/
lemma oplax_left_unitality_of_lax_square [IsIso (ε Q₂)] (a : K₁) [IsIso (e a)]
    [IsIso (μ Q₂ (𝟙_ K₂) (F.obj a))] :
    (λ_ (G.obj (Q₁.obj a))).inv = G.map (λ_ (Q₁.obj a)).inv ≫
      (δG.app (𝟙_ D₁)).app (Q₁.obj a) ≫
        (G.map (ε Q₁) ≫ e (𝟙_ K₁) ≫ Q₂.map (η F) ≫ CategoryTheory.inv (ε Q₂)) ▷
          G.obj (Q₁.obj a) := by
  rw [← cancel_mono ((ε Q₂ ⊗ₘ e a) ≫ μ Q₂ (𝟙_ K₂) (F.obj a))]
  rw [leftUnitor_inv_comp_tensorHom_assoc, LaxMonoidal.left_unitality_inv]
  simp only [assoc]
  rw [whiskerRight_comp_tensorHom_assoc]
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  rw [comp_tensorHom_comp_comp]
  simp only [assoc]
  rw [μ_natural_left, app_app_comp_whiskerRight_assoc, reassoc_of% hδ, ← G.map_comp_assoc,
    ← G.map_comp_assoc, assoc (λ_ (Q₁.obj a)).inv, LaxMonoidal.left_unitality_inv,
    reassoc_of% (he (λ_ a).inv),
    ← Q₂.map_comp, ← Q₂.map_comp, ← OplaxMonoidal.left_unitality]

include hδ he in
/-- The right unitality axiom holds for an object of the form `Q₁ a`, provided the relevant
components of `μ Q₂` and `e` are isomorphisms. -/
lemma oplax_right_unitality_of_lax_square [IsIso (ε Q₂)] (a : K₁) [IsIso (e a)]
    [IsIso (μ Q₂ (F.obj a) (𝟙_ K₂))] :
    (ρ_ (G.obj (Q₁.obj a))).inv = G.map (ρ_ (Q₁.obj a)).inv ≫
      (δG.app (Q₁.obj a)).app (𝟙_ D₁) ≫
        G.obj (Q₁.obj a) ◁
          (G.map (ε Q₁) ≫ e (𝟙_ K₁) ≫ Q₂.map (η F) ≫ CategoryTheory.inv (ε Q₂)) := by
  rw [← cancel_mono ((e a ⊗ₘ ε Q₂) ≫ μ Q₂ (F.obj a) (𝟙_ K₂))]
  rw [rightUnitor_inv_comp_tensorHom_assoc, LaxMonoidal.right_unitality_inv]
  simp only [assoc]
  rw [whiskerLeft_comp_tensorHom_assoc]
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  rw [tensorHom_comp_comp_comp]
  simp only [assoc]
  rw [μ_natural_right, app_app_comp_whiskerLeft_assoc, reassoc_of% hδ, ← G.map_comp_assoc,
    ← G.map_comp_assoc, assoc (ρ_ (Q₁.obj a)).inv, LaxMonoidal.right_unitality_inv,
    reassoc_of% (he (ρ_ a).inv),
    ← Q₂.map_comp, ← Q₂.map_comp, ← OplaxMonoidal.right_unitality]

/-- The oplax monoidal structure on `G : D₁ ⥤ D₂` with comonoidal structure `δG`, induced by
an oplax monoidal functor `F : K₁ ⥤ K₂` through the lax monoidal functors `Q₁ : K₁ ⥤ D₁` and
`Q₂ : K₂ ⥤ D₂`: see the module docstring. Here `e a` only needs to be an isomorphism for the
objects `a` in the class `S`. -/
@[instance_reducible]
noncomputable def ofLaxSquare' [IsIso (ε Q₂)] (S : ObjectProperty K₁)
    (hS : ∀ X : D₁, ∃ a, S a ∧ Nonempty (Q₁.obj a ≅ X))
    (he' : ∀ a, S a → IsIso (e a))
    (hμ : ∀ (x : K₂) (b : K₁), S b → IsIso (μ Q₂ x (F.obj b))) :
    G.OplaxMonoidal where
  η := G.map (ε Q₁) ≫ e (𝟙_ K₁) ≫ Q₂.map (η F) ≫ CategoryTheory.inv (ε Q₂)
  δ X Y := (δG.app X).app Y
  δ_natural_left f X' := app_app_comp_whiskerRight δG X' f
  δ_natural_right X f := app_app_comp_whiskerLeft δG X f
  oplax_associativity X Y Z := by
    obtain ⟨a, ha, ⟨iX⟩⟩ := hS X
    obtain ⟨b, hb, ⟨iY⟩⟩ := hS Y
    obtain ⟨c, hc, ⟨iZ⟩⟩ := hS Z
    have := he' a ha
    have := he' b hb
    have := he' c hc
    have := hμ (F.obj a) b hb
    have := hμ (F.obj a ⊗ F.obj b) c hc
    exact oplax_associativity_of_iso δG iX iY iZ
      (oplax_associativity_of_lax_square δG e he hδ a b c)
  oplax_left_unitality X := by
    obtain ⟨a, ha, ⟨iX⟩⟩ := hS X
    have := he' a ha
    have := LaxMonoidal.isIso_μ_tensorUnit_left Q₂ (F.obj a)
    exact oplax_left_unitality_of_iso δG iX (oplax_left_unitality_of_lax_square δG e he hδ a)
  oplax_right_unitality X := by
    obtain ⟨a, ha, ⟨iX⟩⟩ := hS X
    have := he' a ha
    have := LaxMonoidal.isIso_μ_tensorUnit_right Q₂ (F.obj a)
    exact oplax_right_unitality_of_iso δG iX (oplax_right_unitality_of_lax_square δG e he hδ a)

/-- The oplax monoidal structure on `G : D₁ ⥤ D₂` with comonoidal structure `δG`, induced by
an oplax monoidal functor `F : K₁ ⥤ K₂` through the lax monoidal functors `Q₁ : K₁ ⥤ D₁` and
`Q₂ : K₂ ⥤ D₂`: see the module docstring. -/
@[instance_reducible]
noncomputable def ofLaxSquare [∀ a, IsIso (e a)] [IsIso (ε Q₂)] (S : ObjectProperty K₁)
    (hS : ∀ X : D₁, ∃ a, S a ∧ Nonempty (Q₁.obj a ≅ X))
    (hμ : ∀ (x : K₂) (b : K₁), S b → IsIso (μ Q₂ x (F.obj b))) :
    G.OplaxMonoidal :=
  ofLaxSquare' δG e he hδ S hS (fun _ _ ↦ inferInstance) hμ

end CategoryTheory.Functor.OplaxMonoidal
