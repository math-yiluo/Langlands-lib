/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomTransport

/-!
# Swapping the arguments of iterated internal homs of modules

Let `A` be a commutative monoid in a symmetric monoidal Grothendieck abelian category `C`.

* The swap `Hom_A(a, Hom_A(b, K)) ⟶ Hom_A(b, Hom_A(a, K))`, `f ↦ (y ↦ (x ↦ f x y))`
  (`CategoryTheory.Mod.ihomSwap`). Its twice uncurried form is the twice uncurried identity
  precomposed with the symmetry of the last two variables
  (`CategoryTheory.Mod.uncurryHom_ihomSwap`); it is involutive, hence an isomorphism
  (`CategoryTheory.Mod.ihomSwapIso`), and natural in `K`.
* The swap is compatible with transport along a lax braided functor
  (`CategoryTheory.Mod.map_ihomSwap_comp_trHom`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (G : C ⥤ D) [G.LaxMonoidal]
  (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
    (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)

include hβ in
/-- Transport of the pairing `(f ⊗ y) ⊗ x ↦ e₂ (e₁ (f ⊗ x) ⊗ y)` along a lax braided
functor. -/
lemma tensorHom_associator_braiding_comp {E b a N K : C} {E' b' a' N' K' : D}
    (fE : G.obj E ⟶ E') (fb : G.obj b ⟶ b') (fa : G.obj a ⟶ a') (fN : G.obj N ⟶ N')
    (fK : G.obj K ⟶ K') (e₁ : E ⊗ a ⟶ N) (e₁' : E' ⊗ a' ⟶ N') (e₂ : N ⊗ b ⟶ K)
    (e₂' : N' ⊗ b' ⟶ K') (h₁ : (fE ⊗ₘ fa) ≫ e₁' = Functor.LaxMonoidal.μ G _ _ ≫ G.map e₁ ≫ fN)
    (h₂ : (fN ⊗ₘ fb) ≫ e₂' = Functor.LaxMonoidal.μ G _ _ ≫ G.map e₂ ≫ fK) :
    ((fE ⊗ₘ fb) ⊗ₘ fa) ≫ (α_ E' b' a').hom ≫ E' ◁ (β_ b' a').hom ≫ (α_ E' a' b').inv ≫
        e₁' ▷ b' ≫ e₂' =
      Functor.LaxMonoidal.μ G _ _ ▷ G.obj a ≫ Functor.LaxMonoidal.μ G _ _ ≫
        G.map ((α_ E b a).hom ≫ E ◁ (β_ b a).hom ≫ (α_ E a b).inv ≫ e₁ ▷ b ≫ e₂) ≫ fK := by
  have s₁ : (fE ⊗ₘ (fb ⊗ₘ fa)) ≫ E' ◁ (β_ b' a').hom =
      G.obj E ◁ (β_ _ _).hom ≫ (fE ⊗ₘ (fa ⊗ₘ fb)) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      BraidedCategory.braiding_naturality, Category.comp_id, Category.id_comp]
  have s₂ : ((fE ⊗ₘ fa) ⊗ₘ fb) ≫ e₁' ▷ b' =
      (Functor.LaxMonoidal.μ G _ _ ≫ G.map e₁) ▷ G.obj b ≫ (fN ⊗ₘ fb) := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, h₁, Category.assoc]
  rw [associator_naturality_assoc, reassoc_of% s₁, associator_inv_naturality_assoc,
    reassoc_of% s₂, h₂, G.map_comp, G.map_comp, G.map_comp, G.map_comp]
  simp only [Category.assoc, comp_whiskerRight]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.LaxMonoidal.associativity_inv_assoc,
    Functor.LaxMonoidal.associativity_assoc, ← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← hβ, MonoidalCategory.whiskerLeft_comp_assoc]

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

section Swap

variable (a b K : Mod C A)

/-- The swap `Hom_A(a, Hom_A(b, K)) ⟶ Hom_A(b, Hom_A(a, K))`, `f ↦ (y ↦ (x ↦ f x y))`: the
transpose of `b ⟶ Hom_A(Hom_A(b, K), K) ⟶ Hom_A(Hom_A(a, Hom_A(b, K)), Hom_A(a, K))`,
`y ↦ (g ↦ g y) ↦ (f ↦ (x ↦ f x y))`. -/
noncomputable def ihomSwap : (ihom a).obj ((ihom b).obj K) ⟶ (ihom b).obj ((ihom a).obj K) :=
  transpose (transpose (𝟙 ((ihom b).obj K)) ≫ ihomComp a ((ihom b).obj K) K)

/-- The twice uncurried form of `ihomSwap`: `(f ⊗ y) ⊗ x ↦ f x y`, the twice uncurried identity
precomposed with the symmetry of the last two variables. -/
@[reassoc]
lemma uncurryHom_ihomSwap :
    uncurryHom (ihomSwap a b K) ▷ a.X ≫ evaluation a K =
      (α_ _ _ _).hom ≫ _ ◁ (β_ b.X a.X).hom ≫ (α_ _ _ _).inv ≫
        evaluation a ((ihom b).obj K) ▷ b.X ≫ evaluation b K := by
  rw [ihomSwap, uncurryHom_transpose, uncurryHom_comp, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, uncurryHom_ihomComp, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, ← uncurryHom, uncurryHom_transpose, uncurryHom_id,
    BraidedCategory.braiding_naturality_right_assoc, BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]

/-- `ihomSwap` is involutive. -/
@[reassoc (attr := simp)]
lemma ihomSwap_comp_ihomSwap : ihomSwap a b K ≫ ihomSwap b a K = 𝟙 _ := by
  apply hom_ext₂
  rw [uncurryHom_comp, comp_whiskerRight_assoc, uncurryHom_ihomSwap,
    associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, ← uncurryHom,
    uncurryHom_ihomSwap, Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id_assoc, uncurryHom_id]

/-- The swap `Hom_A(a, Hom_A(b, K)) ≅ Hom_A(b, Hom_A(a, K))` as an isomorphism. -/
@[simps]
noncomputable def ihomSwapIso : (ihom a).obj ((ihom b).obj K) ≅ (ihom b).obj ((ihom a).obj K) where
  hom := ihomSwap a b K
  inv := ihomSwap b a K

/-- `ihomSwap` is an isomorphism. -/
instance isIso_ihomSwap : IsIso (ihomSwap a b K) :=
  (ihomSwapIso a b K).isIso_hom

variable {K} in
/-- `ihomSwap` is natural in `K`. -/
@[reassoc]
lemma ihomSwap_naturality {K' : Mod C A} (f : K ⟶ K') :
    (ihom a).map ((ihom b).map f) ≫ ihomSwap a b K' =
      ihomSwap a b K ≫ (ihom b).map ((ihom a).map f) := by
  apply hom_ext₂
  rw [uncurryHom_comp, comp_whiskerRight_assoc, uncurryHom_ihomSwap,
    associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, evaluation_naturality,
    comp_whiskerRight_assoc, evaluation_naturality, uncurryHom_comp_ihom_map,
    comp_whiskerRight_assoc, evaluation_naturality, uncurryHom_ihomSwap_assoc]

end Swap

section Transport

open scoped Obj

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [SymmetricCategory D] [IsCommMonObj B] [Abelian D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)]
  {G : C ⥤ D} [G.LaxMonoidal] {ρ : B ⟶ G.obj A} [IsMonHom ρ]
  {c : ∀ M N : Mod C A, (mapModComap ρ).obj ((ihom M).obj N) ⟶
    (ihom ((mapModComap ρ).obj M)).obj ((mapModComap ρ).obj N)}
  (hc : ∀ M N : Mod C A,
    uncurryHom (c M N) = Functor.LaxMonoidal.μ G _ _ ≫ G.map (evaluation M N))
  (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
    (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)

include hc hβ in
/-- **`ihomSwap` is compatible with transport along a lax braided functor.** -/
theorem map_ihomSwap_comp_trHom [∀ M N, IsIso (c M N)] {a b K : Mod C A} {a' b' K' : Mod D B}
    (φa : (mapModComap ρ).obj a ≅ a') (φb : (mapModComap ρ).obj b ≅ b')
    (φK : (mapModComap ρ).obj K ≅ K') :
    (mapModComap ρ).map (ihomSwap a b K) ≫ trHom ρ c φb (trIso ρ c φa φK) =
      (trIso ρ c φa (trIso ρ c φb φK)).hom ≫ ihomSwap a' b' K' :=
  map_comp_trHom hc _ φb _ _ _ (tensorHom_comp_eq_of_uncurry hc _ φb φa φK _ _ (by
    rw [uncurryHom_ihomSwap, uncurryHom_ihomSwap]
    exact tensorHom_associator_braiding_comp G hβ _ _ _ _ _ _ _ _ _
      (trHom_evaluation hc φa (trIso ρ c φb φK)) (trHom_evaluation hc φb φK)))

include hc hβ in
/-- `CategoryTheory.Mod.map_ihomSwap_comp_trHom` with the transports given as variables equal
to the iterated transports. -/
theorem map_ihomSwap_comp_of_eq [∀ M N, IsIso (c M N)] {a b K : Mod C A} {a' b' K' : Mod D B}
    (φa : (mapModComap ρ).obj a ≅ a') (φb : (mapModComap ρ).obj b ≅ b')
    (φK : (mapModComap ρ).obj K ≅ K')
    (tbK : (mapModComap ρ).obj ((ihom b).obj K) ≅ (ihom b').obj K')
    (hbK : tbK = trIso ρ c φb φK)
    (taK : (mapModComap ρ).obj ((ihom a).obj K) ≅ (ihom a').obj K')
    (haK : taK = trIso ρ c φa φK)
    (tS : (mapModComap ρ).obj ((ihom a).obj ((ihom b).obj K)) ≅
      (ihom a').obj ((ihom b').obj K'))
    (hS : tS = trIso ρ c φa tbK)
    (tT : (mapModComap ρ).obj ((ihom b).obj ((ihom a).obj K)) ≅
      (ihom b').obj ((ihom a').obj K'))
    (hT : tT = trIso ρ c φb taK) :
    (mapModComap ρ).map (ihomSwap a b K) ≫ tT.hom = tS.hom ≫ ihomSwap a' b' K' := by
  subst hbK haK hS hT
  exact map_ihomSwap_comp_trHom hc hβ φa φb φK

end Transport

end CategoryTheory.Mod
