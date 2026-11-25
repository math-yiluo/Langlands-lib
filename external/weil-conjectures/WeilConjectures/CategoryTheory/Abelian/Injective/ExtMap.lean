/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.CategoryTheory.Sites.SheafCohomology.InjectiveResolution

/-!
# Maps between `Ext` groups induced by maps of cocycles

Let `R`, `R'` be injective resolutions of `Y`, `Y'`. A family of additive maps
`Φₙ : (X ⟶ Rⁿ) →+ (X' ⟶ R'ⁿ)` commuting with the differentials induces additive maps
`Ext X Y n ⟶ Ext X' Y' n` (`CategoryTheory.InjectiveResolution.extMap`), sending the class
`R.extMk f` of a cocycle `f` to `R'.extMk (Φₙ f)`
(`CategoryTheory.InjectiveResolution.extMap_extMk`).
-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Limits

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : InjectiveResolution Y)

/-- A cocycle whose class vanishes is a coboundary, in every degree. -/
lemma extMk_eq_zero_iff_exists {n : ℕ} (f : X ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    R.extMk f (n + 1) rfl hf = 0 ↔
      (n = 0 ∧ f = 0) ∨ ∃ (p : ℕ) (_ : p + 1 = n) (g : X ⟶ R.cocomplex.X p),
        g ≫ R.cocomplex.d p n = f := by
  cases n with
  | zero =>
    rw [R.extMk_eq_zero_iff_of_zero f hf]
    simp
  | succ p =>
    rw [R.extMk_eq_zero_iff f _ rfl hf p rfl]
    simp

variable {X' Y' : C} {R} (R' : InjectiveResolution Y')
  (Φ : ∀ n, (X ⟶ R.cocomplex.X n) →+ (X' ⟶ R'.cocomplex.X n))

omit [HasExt C] in
lemma map_comp_d_eq_zero
    (hΦ : ∀ n m (f : X ⟶ R.cocomplex.X n),
      Φ m (f ≫ R.cocomplex.d n m) = Φ n f ≫ R'.cocomplex.d n m)
    {n : ℕ} (f : X ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) : Φ n f ≫ R'.cocomplex.d n (n + 1) = 0 := by
  rw [← hΦ, hf, map_zero]

/-- Cocycles with the same class are sent to cocycles with the same class. -/
lemma extMk_map_eq_of_extMk_eq
    (hΦ : ∀ n m (f : X ⟶ R.cocomplex.X n),
      Φ m (f ≫ R.cocomplex.d n m) = Φ n f ≫ R'.cocomplex.d n m)
    {n : ℕ} (f g : X ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) (hg : g ≫ R.cocomplex.d n (n + 1) = 0)
    (h : R.extMk f (n + 1) rfl hf = R.extMk g (n + 1) rfl hg) :
    R'.extMk (Φ n f) (n + 1) rfl (map_comp_d_eq_zero R' Φ hΦ f hf) =
      R'.extMk (Φ n g) (n + 1) rfl (map_comp_d_eq_zero R' Φ hΦ g hg) := by
  rw [← sub_eq_zero, sub_extMk] at h ⊢
  rw [R.extMk_eq_zero_iff_exists] at h
  rw [R'.extMk_eq_zero_iff_exists, ← map_sub]
  rcases h with ⟨rfl, h⟩ | ⟨p, hp, k, hk⟩
  · exact Or.inl ⟨rfl, by rw [h, map_zero]⟩
  · exact Or.inr ⟨p, hp, Φ p k, by rw [← hΦ, hk]⟩

/-- The map `Ext X Y n ⟶ Ext X' Y' n` induced by a map of cocycles commuting with the
differentials: the class of a cocycle `f` is sent to the class of `Φₙ f`. -/
noncomputable def extMap
    (hΦ : ∀ n m (f : X ⟶ R.cocomplex.X n),
      Φ m (f ≫ R.cocomplex.d n m) = Φ n f ≫ R'.cocomplex.d n m) (n : ℕ) :
    Ext X Y n →+ Ext X' Y' n :=
  have h (x : Ext X Y n) := R.extMk_surjective x (n + 1) rfl
  let F (x : Ext X Y n) : Ext X' Y' n := R'.extMk (Φ n (h x).choose) (n + 1) rfl
    (map_comp_d_eq_zero R' Φ hΦ _ (h x).choose_spec.choose)
  have hF (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
      F (R.extMk f (n + 1) rfl hf) = R'.extMk (Φ n f) (n + 1) rfl
        (map_comp_d_eq_zero R' Φ hΦ f hf) :=
    extMk_map_eq_of_extMk_eq R' Φ hΦ _ _ _ hf (h _).choose_spec.choose_spec
  AddMonoidHom.mk' F fun x y ↦ by
    obtain ⟨f, hf, rfl⟩ := h x
    obtain ⟨g, hg, rfl⟩ := h y
    simp only [add_extMk, hF, map_add]

lemma extMap_extMk
    (hΦ : ∀ n m (f : X ⟶ R.cocomplex.X n),
      Φ m (f ≫ R.cocomplex.d n m) = Φ n f ≫ R'.cocomplex.d n m)
    {n : ℕ} (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    extMap R' Φ hΦ n (R.extMk f (n + 1) rfl hf) =
      R'.extMk (Φ n f) (n + 1) rfl (map_comp_d_eq_zero R' Φ hΦ f hf) :=
  extMk_map_eq_of_extMk_eq R' Φ hΦ _ _ _ hf
    (R.extMk_surjective _ (n + 1) rfl).choose_spec.choose_spec

lemma extMap_congr {Φ' : ∀ n, (X ⟶ R.cocomplex.X n) →+ (X' ⟶ R'.cocomplex.X n)}
    (hΦ : ∀ n m (f : X ⟶ R.cocomplex.X n),
      Φ m (f ≫ R.cocomplex.d n m) = Φ n f ≫ R'.cocomplex.d n m)
    (hΦ' : ∀ n m (f : X ⟶ R.cocomplex.X n),
      Φ' m (f ≫ R.cocomplex.d n m) = Φ' n f ≫ R'.cocomplex.d n m) (h : Φ = Φ') (n : ℕ) :
    extMap R' Φ hΦ n = extMap R' Φ' hΦ' n := by
  subst h
  rfl

end CategoryTheory.InjectiveResolution
