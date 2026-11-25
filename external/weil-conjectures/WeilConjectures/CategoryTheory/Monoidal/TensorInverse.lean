/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Integer tensor powers of an invertible object

Let `L` be an object of a monoidal category `C` with a two-sided tensor inverse `M`:
`L ⊗ M ≅ 𝟙` and `M ⊗ L ≅ 𝟙` (`CategoryTheory.MonoidalCategory.TensorInverse`). This file
constructs *coherent* integer tensor powers `L^{⊗ m}`, `m ∈ ℤ`: objects
`CategoryTheory.MonoidalCategory.TensorInverse.zpow` with `L^{⊗ 0} = 𝟙`, `L^{⊗ 1} ≅ L`, and
identifications `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ c}` for `a + b = c` satisfying the unit laws and the
associativity law. In other words, an invertible object generates a monoidal functor out of the
discrete monoidal category `ℤ`.

## Construction

`L^{⊗ m}` is `L ⊗ (L ⊗ ⋯ ⊗ 𝟙)` for `m ≥ 0` and `M ⊗ (M ⊗ ⋯ ⊗ 𝟙)` for `m < 0`; in every case
there is a *successor isomorphism* `L^{⊗ (a + 1)} ≅ L ⊗ L^{⊗ a}`
(`CategoryTheory.MonoidalCategory.TensorInverse.succIso`), which only uses `L ⊗ M ≅ 𝟙`. The
product `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}` is the left unitor for `a = 0` and is determined for
the other `a` by the *recursion*

```
L^{⊗ (a+1)} ⊗ L^{⊗ b} ≅ (L ⊗ L^{⊗ a}) ⊗ L^{⊗ b} ≅ L ⊗ (L^{⊗ a} ⊗ L^{⊗ b}) ≅ L ⊗ L^{⊗ (a+b)}
  ≅ L^{⊗ (a+b+1)}
```

read forwards for `a ≥ 0` and backwards for `a < 0`; reading it backwards means dividing by
`L ⊗ -`, which is possible because `L ⊗ -` is an equivalence of categories, with inverse
`M ⊗ -`. The recursion then holds for *every* `a`
(`CategoryTheory.MonoidalCategory.TensorInverse.addIso_succ`), and since `L ⊗ -` is faithful
the unit and associativity laws for `a + 1` are equivalent to those for `a`: they follow by
induction from the case `a = 0`, which is the coherence of the unitors.

## Main definitions

- `CategoryTheory.MonoidalCategory.TensorInverse`: a two-sided tensor inverse of an object.
- `CategoryTheory.MonoidalCategory.TensorInverse.zpow`: the tensor power `L^{⊗ m}`, `m ∈ ℤ`.
- `CategoryTheory.MonoidalCategory.TensorInverse.addIso`:
  `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ c}` for `a + b = c`.

## Main statements

- `CategoryTheory.MonoidalCategory.TensorInverse.addIso_zero_left`,
  `CategoryTheory.MonoidalCategory.TensorInverse.addIso_zero_right`: the unit laws.
- `CategoryTheory.MonoidalCategory.TensorInverse.addIso_assoc`: the associativity law.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Category

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A *two-sided tensor inverse* of an object `L` of a monoidal category: an object `M` with
`L ⊗ M ≅ 𝟙` and `M ⊗ L ≅ 𝟙`. -/
structure TensorInverse (L : C) where
  /-- The inverse object `M`. -/
  obj : C
  /-- The identification `L ⊗ M ≅ 𝟙`. -/
  rightIso : L ⊗ obj ≅ 𝟙_ C
  /-- The identification `M ⊗ L ≅ 𝟙`. -/
  leftIso : obj ⊗ L ≅ 𝟙_ C

/-- The `n`-th tensor power `X ⊗ (X ⊗ ⋯ ⊗ 𝟙)` of an object, `n ∈ ℕ`. -/
noncomputable def tensorPowNat (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => X ⊗ tensorPowNat X n

namespace TensorInverse

variable {L : C} (e : TensorInverse L)

/-- Tensoring on the left with an object with a two-sided tensor inverse is an equivalence of
categories, with inverse tensoring with the inverse. -/
noncomputable def tensorLeftEquivalence : C ≌ C :=
  Equivalence.mk (tensorLeft L) (tensorLeft e.obj)
    (NatIso.ofComponents
      (fun X ↦ (λ_ X).symm ≪≫ whiskerRightIso e.leftIso.symm X ≪≫ α_ _ _ _)
      (fun f ↦ by
        simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
          Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
        dsimp
        rw [← associator_naturality_right, ← whisker_exchange_assoc,
          leftUnitor_inv_naturality_assoc]))
    (NatIso.ofComponents
      (fun X ↦ (α_ _ _ _).symm ≪≫ whiskerRightIso e.rightIso X ≪≫ λ_ X)
      (fun f ↦ by
        simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
          Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
        dsimp
        rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
          leftUnitor_naturality]))

/-- `L ⊗ -` is fully faithful. -/
noncomputable def fullyFaithfulTensorLeft : (tensorLeft L).FullyFaithful :=
  e.tensorLeftEquivalence.fullyFaithfulFunctor

include e in
lemma whiskerLeft_injective {X Y : C} {f g : X ⟶ Y} (h : L ◁ f = L ◁ g) : f = g :=
  e.fullyFaithfulTensorLeft.map_injective h

/-- The tensor power `L^{⊗ m}`, `m ∈ ℤ`: `L ⊗ (L ⊗ ⋯ ⊗ 𝟙)` for `m ≥ 0` and
`M ⊗ (M ⊗ ⋯ ⊗ 𝟙)` (with `-m` factors) for `m < 0`. -/
noncomputable def zpow : ℤ → C
  | .ofNat n => tensorPowNat L n
  | .negSucc n => tensorPowNat e.obj (n + 1)

@[simp]
lemma zpow_zero : e.zpow 0 = 𝟙_ C := rfl

/-- The successor isomorphism `L^{⊗ (a + 1)} ≅ L ⊗ L^{⊗ a}`, stated for the index `a + 1`
itself. -/
noncomputable def succIso' : (a : ℤ) → e.zpow (a + 1) ≅ L ⊗ e.zpow a
  | .ofNat _ => Iso.refl _
  | .negSucc 0 => e.rightIso.symm ≪≫ whiskerLeftIso L (ρ_ e.obj).symm
  | .negSucc (_ + 1) => (λ_ _).symm ≪≫ whiskerRightIso e.rightIso.symm _ ≪≫ α_ _ _ _

/-- The successor isomorphism `L^{⊗ a'} ≅ L ⊗ L^{⊗ a}` for `a + 1 = a'`. -/
noncomputable def succIso (a a' : ℤ) (h : a + 1 = a') : e.zpow a' ≅ L ⊗ e.zpow a :=
  eqToIso (congrArg e.zpow h.symm) ≪≫ e.succIso' a

/-- One step of the recursion defining the products of tensor powers, read forwards: from
`L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ c}` to `L^{⊗ a'} ⊗ L^{⊗ b} ≅ L^{⊗ c'}` for `a' = a + 1`,
`c' = c + 1`. -/
noncomputable def ascend {a a' b c c' : ℤ} (ha : a + 1 = a') (hc : c + 1 = c')
    (μ : e.zpow a ⊗ e.zpow b ≅ e.zpow c) : e.zpow a' ⊗ e.zpow b ≅ e.zpow c' :=
  whiskerRightIso (e.succIso a a' ha) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso L μ ≪≫
    (e.succIso c c' hc).symm

/-- One step of the recursion defining the products of tensor powers, read backwards: from
`L^{⊗ a'} ⊗ L^{⊗ b} ≅ L^{⊗ c'}` to `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ c}` for `a' = a + 1`,
`c' = c + 1`, dividing by the fully faithful functor `L ⊗ -`. -/
noncomputable def descend {a a' b c c' : ℤ} (ha : a + 1 = a') (hc : c + 1 = c')
    (μ : e.zpow a' ⊗ e.zpow b ≅ e.zpow c') : e.zpow a ⊗ e.zpow b ≅ e.zpow c :=
  e.fullyFaithfulTensorLeft.preimageIso
    ((α_ _ _ _).symm ≪≫ whiskerRightIso (e.succIso a a' ha).symm _ ≪≫ μ ≪≫
      e.succIso c c' hc)

lemma whiskerLeft_descend_hom {a a' b c c' : ℤ} (ha : a + 1 = a') (hc : c + 1 = c')
    (μ : e.zpow a' ⊗ e.zpow b ≅ e.zpow c') :
    L ◁ (e.descend ha hc μ).hom = (α_ _ _ _).inv ≫ (e.succIso a a' ha).inv ▷ _ ≫ μ.hom ≫
      (e.succIso c c' hc).hom := by
  exact e.fullyFaithfulTensorLeft.map_preimage _

/-- The products `L^{⊗ n} ⊗ L^{⊗ b} ≅ L^{⊗ (n + b)}` for `n ∈ ℕ`. -/
noncomputable def addIsoNat (b : ℤ) : (n : ℕ) → e.zpow n ⊗ e.zpow b ≅ e.zpow (n + b)
  | 0 => λ_ _ ≪≫ eqToIso (by simp)
  | n + 1 => e.ascend (by push_cast; rfl) (by push_cast; ring) (addIsoNat b n)

/-- The products `L^{⊗ (-n-1)} ⊗ L^{⊗ b} ≅ L^{⊗ (-n-1+b)}` for `n ∈ ℕ`. -/
noncomputable def addIsoNeg (b : ℤ) : (n : ℕ) → e.zpow (.negSucc n) ⊗ e.zpow b ≅
    e.zpow (.negSucc n + b)
  | 0 => e.descend (a' := ((0 : ℕ) : ℤ)) (by rfl) (by rw [Int.negSucc_eq]; ring)
      (e.addIsoNat b 0)
  | n + 1 => e.descend (a' := .negSucc n) (by rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring)
      (by rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring) (addIsoNeg b n)

/-- The products `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}`. -/
noncomputable def addIso' : (a b : ℤ) → e.zpow a ⊗ e.zpow b ≅ e.zpow (a + b)
  | .ofNat n, b => e.addIsoNat b n
  | .negSucc n, b => e.addIsoNeg b n

/-- The identification `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ c}` for `a + b = c`. -/
noncomputable def addIso (a b c : ℤ) (h : a + b = c) : e.zpow a ⊗ e.zpow b ≅ e.zpow c :=
  e.addIso' a b ≪≫ eqToIso (congrArg e.zpow h)

lemma addIso_congr {a b c c' : ℤ} (h : a + b = c) (h' : a + b = c') :
    (e.addIso a b c h).hom ≫ eqToHom (congrArg e.zpow (h.symm.trans h')) =
      (e.addIso a b c' h').hom := by
  subst h h'
  simp


lemma addIso_hom_eqToHom {a b c c' : ℤ} (h : a + b = c) (hc : c = c') :
    (e.addIso a b c h).hom ≫ eqToHom (congrArg e.zpow hc) = (e.addIso a b c' (h.trans hc)).hom := by
  subst hc
  simp

lemma eqToHom_addIso_hom {a a' b c : ℤ} (ha : a = a') (h : a' + b = c) :
    eqToHom (congrArg e.zpow ha) ▷ e.zpow b ≫ (e.addIso a' b c h).hom =
      (e.addIso a b c (ha ▸ h)).hom := by
  subst ha
  simp

/-- The left unit law at the level of the defining recursion: `L^{⊗ 0} ⊗ L^{⊗ b} ≅ L^{⊗ b}` is
the left unitor. -/
lemma addIso_zero_left (b c : ℤ) (h : 0 + b = c) :
    (e.addIso 0 b c h).hom =
      (λ_ _).hom ≫ eqToHom (congrArg e.zpow ((zero_add b).symm.trans h)) := by
  subst h
  simp [addIso, addIso', addIsoNat]

/-- The defining recursion of the products of tensor powers, valid for every `a ∈ ℤ`:
```
L^{⊗ a'} ⊗ L^{⊗ b} ≅ (L ⊗ L^{⊗ a}) ⊗ L^{⊗ b} ≅ L ⊗ (L^{⊗ a} ⊗ L^{⊗ b}) ≅ L ⊗ L^{⊗ c} ≅ L^{⊗ c'}
```
for `a' = a + 1`, `a + b = c` and `c' = c + 1`. -/
lemma addIso_succ (a a' b c c' : ℤ) (ha : a + 1 = a') (h : a + b = c) (h' : a' + b = c')
    (hc : c + 1 = c') :
    (e.addIso a' b c' h').hom = (e.succIso a a' ha).hom ▷ _ ≫ (α_ _ _ _).hom ≫
      L ◁ (e.addIso a b c h).hom ≫ (e.succIso c c' hc).inv := by
  rcases a with n | n
  · obtain rfl : a' = ((n + 1 : ℕ) : ℤ) := by rw [← ha]; rfl
    obtain rfl : c = (n : ℤ) + b := h.symm
    obtain rfl : c' = ((n + 1 : ℕ) : ℤ) + b := h'.symm
    simp only [addIso, addIso', Iso.trans_hom, eqToIso_refl, Iso.refl_hom, comp_id]
    rfl
  · rcases n with _ | k
    · obtain rfl : a' = ((0 : ℕ) : ℤ) := by rw [← ha]; rfl
      obtain rfl : c = Int.negSucc 0 + b := h.symm
      obtain rfl : c' = ((0 : ℕ) : ℤ) + b := h'.symm
      simp only [addIso, addIso', Iso.trans_hom, eqToIso_refl, Iso.refl_hom, comp_id, addIsoNeg,
        whiskerLeft_descend_hom]
      simp
    · obtain rfl : a' = Int.negSucc k := by
        rw [← ha, Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
      obtain rfl : c = Int.negSucc (k + 1) + b := h.symm
      obtain rfl : c' = Int.negSucc k + b := h'.symm
      simp only [addIso, addIso', Iso.trans_hom, eqToIso_refl, Iso.refl_hom, comp_id, addIsoNeg,
        whiskerLeft_descend_hom]
      simp


/-- A property of integers that holds at `0` and passes between consecutive integers holds
everywhere. -/
private lemma int_induction_of_iff {P : ℤ → Prop} (h₀ : P 0) (h : ∀ a, P a ↔ P (a + 1))
    (a : ℤ) : P a := by
  induction a using Int.induction_on with
  | zero => exact h₀
  | succ i hi => exact (h _).1 hi
  | pred i hi => exact (h _).2 (by simpa using hi)

/-- The right unit law: `L^{⊗ a} ⊗ L^{⊗ 0} ≅ L^{⊗ a}` is the right unitor. -/
lemma addIso_zero_right (a c : ℤ) (h : a + 0 = c) :
    (e.addIso a 0 c h).hom =
      (ρ_ _).hom ≫ eqToHom (congrArg e.zpow ((add_zero a).symm.trans h)) := by
  subst h
  rw [← e.addIso_hom_eqToHom (add_zero a) (add_zero a).symm]
  congr 1
  revert a
  refine int_induction_of_iff (P := fun a ↦ (e.addIso a 0 a (add_zero a)).hom = (ρ_ _).hom) ?_ ?_
  · rw [addIso_zero_left]
    simp [unitors_equal]
  · intro a
    have key := e.addIso_succ a (a + 1) 0 a (a + 1) rfl (add_zero a) (add_zero _) rfl
    have hρ : (e.succIso a (a + 1) rfl).hom ▷ e.zpow 0 ≫ (α_ _ _ _).hom ≫
        L ◁ (ρ_ (e.zpow a)).hom ≫ (e.succIso a (a + 1) rfl).inv = (ρ_ (e.zpow (a + 1))).hom := by
      dsimp only [zpow_zero]
      rw [whiskerLeft_rightUnitor]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [rightUnitor_naturality_assoc, Iso.hom_inv_id, comp_id]
    rw [key, ← hρ]
    constructor
    · intro ha
      rw [ha]
    · intro ha
      simp only [cancel_epi, cancel_mono] at ha
      exact e.whiskerLeft_injective ha

/-- The associativity law of the products of tensor powers:
```
(L^{⊗ a} ⊗ L^{⊗ b}) ⊗ L^{⊗ c} ─────α─────▶ L^{⊗ a} ⊗ (L^{⊗ b} ⊗ L^{⊗ c})
            │                                          │
            ▼                                          ▼
     L^{⊗ d} ⊗ L^{⊗ c} ──────▶ L^{⊗ f} ◀────── L^{⊗ a} ⊗ L^{⊗ e'}
```
for `a + b = d`, `b + c = e'` and `d + c = a + e' = f`. -/
lemma addIso_assoc (a b c d e' f : ℤ) (hab : a + b = d) (hbc : b + c = e') (hd : d + c = f)
    (he : a + e' = f) :
    (e.addIso a b d hab).hom ▷ e.zpow c ≫ (e.addIso d c f hd).hom =
      (α_ _ _ _).hom ≫ e.zpow a ◁ (e.addIso b c e' hbc).hom ≫ (e.addIso a e' f he).hom := by
  subst hab hbc hd
  revert b c
  refine int_induction_of_iff (P := fun a ↦ ∀ b c (he : a + (b + c) = a + b + c),
    (e.addIso a b (a + b) rfl).hom ▷ e.zpow c ≫ (e.addIso (a + b) c (a + b + c) rfl).hom =
      (α_ _ _ _).hom ≫ e.zpow a ◁ (e.addIso b c (b + c) rfl).hom ≫
        (e.addIso a (b + c) (a + b + c) he).hom) ?_ ?_ a
  · intro b c he
    have h1 := e.addIso_zero_left b (0 + b) rfl
    have h2 := e.addIso_zero_left (b + c) (0 + b + c) he
    rw [h1, h2, comp_whiskerRight, Category.assoc, e.eqToHom_addIso_hom (zero_add b).symm]
    dsimp only [zpow_zero]
    rw [leftUnitor_naturality_assoc, leftUnitor_whiskerRight, Category.assoc,
      e.addIso_hom_eqToHom]
    ring
  · intro a
    have key : ∀ b c (he : a + (b + c) = a + b + c) (he' : a + 1 + (b + c) = a + 1 + b + c),
        ((e.addIso (a + 1) b (a + 1 + b) rfl).hom ▷ e.zpow c ≫
          (e.addIso (a + 1 + b) c (a + 1 + b + c) rfl).hom =
          (α_ _ _ _).hom ≫ e.zpow (a + 1) ◁ (e.addIso b c (b + c) rfl).hom ≫
            (e.addIso (a + 1) (b + c) (a + 1 + b + c) he').hom) ↔
        ((e.addIso a b (a + b) rfl).hom ▷ e.zpow c ≫ (e.addIso (a + b) c (a + b + c) rfl).hom =
          (α_ _ _ _).hom ≫ e.zpow a ◁ (e.addIso b c (b + c) rfl).hom ≫
            (e.addIso a (b + c) (a + b + c) he).hom) := by
      intro b c he he'
      have k1 := e.addIso_succ a (a + 1) b (a + b) (a + 1 + b) rfl rfl rfl (by ring)
      have k2 := e.addIso_succ (a + b) (a + 1 + b) c (a + b + c) (a + 1 + b + c) (by ring) rfl
        rfl (by ring)
      have k3 := e.addIso_succ a (a + 1) (b + c) (a + b + c) (a + 1 + b + c) rfl he he' (by ring)
      rw [k1, k2, k3]
      set sa := e.succIso a (a + 1) rfl
      set sab := e.succIso (a + b) (a + 1 + b) (by ring)
      set sabc := e.succIso (a + b + c) (a + 1 + b + c) (by ring)
      have hA : (sa.hom ▷ e.zpow b ≫ (α_ _ _ _).hom ≫ L ◁ (e.addIso a b (a + b) rfl).hom ≫
            sab.inv) ▷ e.zpow c ≫ (sab.hom ▷ e.zpow c ≫ (α_ _ _ _).hom ≫
            L ◁ (e.addIso (a + b) c (a + b + c) rfl).hom ≫ sabc.inv) =
          ((sa.hom ▷ e.zpow b) ▷ e.zpow c ≫ (α_ _ _ _).hom ▷ e.zpow c ≫ (α_ _ _ _).hom) ≫
            L ◁ ((e.addIso a b (a + b) rfl).hom ▷ e.zpow c ≫
              (e.addIso (a + b) c (a + b + c) rfl).hom) ≫ sabc.inv := by
        simp only [comp_whiskerRight, Category.assoc, inv_hom_whiskerRight_assoc,
          whiskerLeft_comp]
        rw [associator_naturality_middle_assoc]
      have hB : (α_ _ _ _).hom ≫ e.zpow (a + 1) ◁ (e.addIso b c (b + c) rfl).hom ≫
            (sa.hom ▷ e.zpow (b + c) ≫ (α_ _ _ _).hom ≫
              L ◁ (e.addIso a (b + c) (a + b + c) he).hom ≫ sabc.inv) =
          ((sa.hom ▷ e.zpow b) ▷ e.zpow c ≫ (α_ _ _ _).hom ▷ e.zpow c ≫ (α_ _ _ _).hom) ≫
            L ◁ ((α_ _ _ _).hom ≫ e.zpow a ◁ (e.addIso b c (b + c) rfl).hom ≫
              (e.addIso a (b + c) (a + b + c) he).hom) ≫ sabc.inv := by
        rw [whisker_exchange_assoc, associator_naturality_right_assoc,
          ← associator_naturality_left_assoc]
        simp only [whiskerLeft_comp, Category.assoc]
        monoidal
      rw [hA, hB]
      constructor
      · intro h
        simp only [cancel_epi, cancel_mono] at h
        exact e.whiskerLeft_injective h
      · intro h
        rw [h]
    constructor
    · intro H b c he
      exact (key b c (by ring) he).2 (H b c _)
    · intro H b c he
      exact (key b c he (by ring)).1 (H b c _)

end TensorInverse

end CategoryTheory.MonoidalCategory
