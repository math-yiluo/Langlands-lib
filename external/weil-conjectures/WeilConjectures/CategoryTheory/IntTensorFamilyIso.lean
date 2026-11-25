/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily

/-!
# Isomorphisms of integer tensor families

A comparison in degree one uniquely extends to a multiplicative comparison of
coherent integer tensor families. Source: the universal property of the group of integers.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v w
namespace CategoryTheory.MonoidalCategory.IntTensorFamily
open Category
variable {C : Type w} [Category.{v} C] [MonoidalCategory C]

/-- Each member of an integer tensor family is tensor invertible. -/
def tensorInverse (P : IntTensorFamily C) (a : ℤ) : TensorInverse (P.obj a) where
  obj := P.obj (-a)
  rightIso := P.addIso a (-a) ≪≫ eqToIso (congrArg P.obj (add_neg_cancel a)) ≪≫ P.zeroIso
  leftIso := P.addIso (-a) a ≪≫ eqToIso (congrArg P.obj (neg_add_cancel a)) ≪≫ P.zeroIso

/-- Multiplication with an explicitly specified sum. -/
def mulIso (P : IntTensorFamily C) (a b c : ℤ) (h : a + b = c) :
    P.obj a ⊗ P.obj b ≅ P.obj c := P.addIso a b ≪≫ eqToIso (congrArg P.obj h)

@[simp] theorem mulIso_rfl (P : IntTensorFamily C) (a b : ℤ) :
    P.mulIso a b (a + b) rfl = P.addIso a b := by
  apply Iso.ext
  simp [mulIso]

/-- Successor multiplication in a coherent family. -/
def step (P : IntTensorFamily C) (a : ℤ) : P.obj 1 ⊗ P.obj a ≅ P.obj (a + 1) :=
  P.mulIso 1 a (a + 1) (add_comm 1 a)

variable (P Q : IntTensorFamily C) (e : P.obj 1 ≅ Q.obj 1)

/-- Extension to nonnegative indices. -/
def isoNat : (n : ℕ) → P.obj (.ofNat n) ≅ Q.obj (.ofNat n)
  | 0 => P.zeroIso ≪≫ Q.zeroIso.symm
  | n + 1 => (P.step n).symm ≪≫ tensorIso e (isoNat n) ≪≫ Q.step n

/-- Extension downwards, using the inverse of tensoring by the degree-one object. -/
def isoNeg : (n : ℕ) → P.obj (-(n : ℤ)) ≅ Q.obj (-(n : ℤ))
  | 0 => P.zeroIso ≪≫ Q.zeroIso.symm
  | n + 1 => (Q.tensorInverse 1).fullyFaithfulTensorLeft.preimageIso
      (whiskerRightIso e.symm _ ≪≫
        P.mulIso 1 (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) ≪≫
        isoNeg n ≪≫
        (Q.mulIso 1 (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).symm)

/-- The objectwise comparison extending the prescribed degree-one isomorphism. -/
def iso : (a : ℤ) → P.obj a ≅ Q.obj a
  | .ofNat n => isoNat P Q e n
  | .negSucc n => isoNeg P Q e (n + 1)

@[simp] theorem iso_zero : iso P Q e 0 = P.zeroIso ≪≫ Q.zeroIso.symm := rfl

@[simp] theorem iso_neg_nat (n : ℕ) :
    iso P Q e (-(n : ℤ)) = isoNeg P Q e n := by
  cases n <;> rfl

/-- Extension respects successor multiplication. -/
theorem iso_step (a : ℤ) :
    (P.step a).hom ≫ (iso P Q e (a + 1)).hom =
      tensorHom e.hom (iso P Q e a).hom ≫ (Q.step a).hom := by
  cases a with
  | ofNat n =>
    change (P.step (n : ℤ)).hom ≫
      ((P.step (n : ℤ)).symm ≪≫ tensorIso e (isoNat P Q e n) ≪≫ Q.step (n : ℤ)).hom = _
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, tensorIso_hom]
    rfl
  | negSucc n =>
    have h := (Q.tensorInverse 1).fullyFaithfulTensorLeft.map_preimage
      (whiskerRightIso e.symm (P.obj (-((n + 1 : ℕ) : ℤ))) ≪≫
        P.mulIso 1 (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) ≪≫
        isoNeg P Q e n ≪≫
        (Q.mulIso 1 (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).symm).hom
    change Q.obj 1 ◁ (isoNeg P Q e (n + 1)).hom = _ at h
    change _ = tensorHom e.hom (isoNeg P Q e (n + 1)).hom ≫ _
    rw [tensorHom_def, h]
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
    have hs : Int.negSucc n + 1 = -(n : ℤ) := by omega
    have hi : iso P Q e (Int.negSucc n + 1) =
        eqToIso (congrArg P.obj hs) ≪≫ isoNeg P Q e n ≪≫
          eqToIso (congrArg Q.obj hs.symm) := by
      have hi' := iso_neg_nat P Q e n
      generalize Int.negSucc n + 1 = k at hs ⊢
      subst hs
      simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl] using hi'
    rw [hi]
    simp only [step, mulIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
    simp only [Iso.trans_inv, eqToIso.inv, hom_inv_whiskerRight_assoc,
      Category.assoc, eqToHom_refl,
      Category.comp_id]
    have hn : -((n + 1 : ℕ) : ℤ) = Int.negSucc n := by omega
    erw [Iso.inv_hom_id]
    rw [Category.comp_id]
    simp only [Category.id_comp]
    rfl

/-- Associativity with all three sums explicitly identified. -/
theorem mulIso_assoc (P : IntTensorFamily C) (a b c d e f : ℤ)
    (hab : a + b = d) (hbc : b + c = e) (hd : d + c = f) (he : a + e = f) :
    (P.mulIso a b d hab).hom ▷ P.obj c ≫ (P.mulIso d c f hd).hom =
      (α_ _ _ _).hom ≫ P.obj a ◁ (P.mulIso b c e hbc).hom ≫
        (P.mulIso a e f he).hom := by
  subst hab hbc hd
  simp only [mulIso, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  rw [P.assoc]

/-- Associativity for multiplication by the degree-one object. -/
theorem step_assoc (P : IntTensorFamily C) (a b : ℤ) :
    (P.step a).hom ▷ P.obj b ≫
        (P.mulIso (a + 1) b (a + b + 1) (by omega)).hom =
      (α_ _ _ _).hom ≫ P.obj 1 ◁ (P.addIso a b).hom ≫ (P.step (a + b)).hom := by
  simpa only [step, mulIso_rfl] using
    P.mulIso_assoc 1 a b (a + 1) (a + b) (a + b + 1)
      (by omega) rfl (by omega) (by omega)

/-- Any objectwise comparison commutes with equality transports of indices. -/
theorem iso_naturality (s : ∀ a, P.obj a ≅ Q.obj a) {a b : ℤ} (h : a = b) :
    (s a).hom ≫ eqToHom (congrArg Q.obj h) =
      eqToHom (congrArg P.obj h) ≫ (s b).hom := by
  subst h
  simp

/-- The extension agrees with the prescribed comparison in degree one. -/
@[simp] theorem iso_one : iso P Q e 1 = e := by
  apply Iso.ext
  change (P.step 0).inv ≫ tensorHom e.hom (P.zeroIso ≪≫ Q.zeroIso.symm).hom ≫
    (Q.step 0).hom = e.hom
  have hp : (P.step 0).hom = P.obj 1 ◁ P.zeroIso.hom ≫ (ρ_ (P.obj 1)).hom := by
    simpa only [step, mulIso, Iso.trans_hom, eqToIso.hom, add_zero,
      eqToHom_refl, Category.comp_id] using (P.zero_right 1).symm
  have hq : (Q.step 0).hom = Q.obj 1 ◁ Q.zeroIso.hom ≫ (ρ_ (Q.obj 1)).hom := by
    simpa only [step, mulIso, Iso.trans_hom, eqToIso.hom, add_zero,
      eqToHom_refl, Category.comp_id] using (Q.zero_right 1).symm
  rw [← cancel_epi (P.step 0).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [hp, hq]
  simp only [tensorHom_def, Iso.trans_hom, Iso.symm_hom,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc (Q.obj 1) Q.zeroIso.inv Q.zeroIso.hom,
    Q.zeroIso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [← whisker_exchange_assoc]
  exact congrArg (fun f ↦ P.obj 1 ◁ P.zeroIso.hom ≫ f) (rightUnitor_naturality e.hom)

private lemma int_induction_of_iff {P : ℤ → Prop} (h₀ : P 0)
    (h : ∀ a, P a ↔ P (a + 1)) (a : ℤ) : P a := by
  induction a using Int.induction_on with
  | zero => exact h₀
  | succ i hi => exact (h _).1 hi
  | pred i hi => exact (h _).2 (by simpa using hi)

/-- Extension is compatible with all integer products. -/
theorem iso_mul (a b c : ℤ) (h : a + b = c) :
    (P.mulIso a b c h).hom ≫ (iso P Q e c).hom =
      tensorHom (iso P Q e a).hom (iso P Q e b).hom ≫ (Q.mulIso a b c h).hom := by
  revert b c
  refine int_induction_of_iff (P := fun a ↦ ∀ b c (h : a + b = c),
    (P.mulIso a b c h).hom ≫ (iso P Q e c).hom =
      tensorHom (iso P Q e a).hom (iso P Q e b).hom ≫ (Q.mulIso a b c h).hom) ?_ ?_ a
  · intro b c h
    subst c
    simp only [mulIso_rfl]
    rw [← cancel_mono (eqToHom (congrArg Q.obj (zero_add b)))]
    simp only [Category.assoc]
    rw [iso_naturality P Q (iso P Q e) (zero_add b),
      ← Category.assoc, ← P.zero_left, ← Q.zero_left]
    simp only [iso_zero, Iso.trans_hom, Iso.symm_hom, tensorHom_def,
      comp_whiskerRight, Category.assoc]
    rw [← leftUnitor_naturality]
    rw [← whisker_exchange_assoc Q.zeroIso.inv (iso P Q e b).hom,
      inv_hom_whiskerRight_assoc]
  · intro a
    have key (b c : ℤ) (h : a + b = c) :
        ((P.mulIso (a + 1) b (c + 1) (by omega)).hom ≫ (iso P Q e (c + 1)).hom =
          tensorHom (iso P Q e (a + 1)).hom (iso P Q e b).hom ≫
            (Q.mulIso (a + 1) b (c + 1) (by omega)).hom) ↔
        ((P.mulIso a b c h).hom ≫ (iso P Q e c).hom =
          tensorHom (iso P Q e a).hom (iso P Q e b).hom ≫
            (Q.mulIso a b c h).hom) := by
      rw [← cancel_epi ((P.step a).hom ▷ P.obj b)]
      have hp : (P.step a).hom ▷ P.obj b ≫
          (P.mulIso (a + 1) b (c + 1) (by omega)).hom =
          (α_ _ _ _).hom ≫ P.obj 1 ◁ (P.mulIso a b c h).hom ≫ (P.step c).hom := by
        subst h
        simpa only [mulIso_rfl] using P.step_assoc a b
      have hq : (Q.step a).hom ▷ Q.obj b ≫
          (Q.mulIso (a + 1) b (c + 1) (by omega)).hom =
          (α_ _ _ _).hom ≫ Q.obj 1 ◁ (Q.mulIso a b c h).hom ≫ (Q.step c).hom := by
        subst h
        simpa only [mulIso_rfl] using Q.step_assoc a b
      have ht : (P.step a).hom ▷ P.obj b ≫
          tensorHom (iso P Q e (a + 1)).hom (iso P Q e b).hom =
          tensorHom (tensorHom e.hom (iso P Q e a).hom) (iso P Q e b).hom ≫
            (Q.step a).hom ▷ Q.obj b := by
        simp only [tensorHom_def, ← comp_whiskerRight_assoc]
        rw [iso_step]
        simp only [tensorHom_def, comp_whiskerRight, Category.assoc]
        rw [← whisker_exchange (Q.step a).hom (iso P Q e b).hom]
      rw [reassoc_of% hp, reassoc_of% ht]
      rw [iso_step, hq, associator_naturality_assoc]
      simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← whisker_exchange_assoc e.hom (Q.mulIso a b c h).hom]
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
      simp only [cancel_epi, cancel_mono]
      constructor
      · intro h
        exact (P.tensorInverse 1).whiskerLeft_injective h
      · intro h
        rw [h]
    constructor
    · intro H b c h
      obtain ⟨d, rfl⟩ : ∃ d : ℤ, c = d + 1 := ⟨c - 1, by omega⟩
      have h' : a + b = d := by omega
      exact (key b d h').2 (H b d h')
    · intro H b c h
      exact (key b c h).1 (H b (c + 1) (by omega))

/-- A comparison is determined by its value at zero and its successor equations. -/
theorem iso_unique_of_step (s : ∀ a, P.obj a ≅ Q.obj a)
    (hzero : s 0 = P.zeroIso ≪≫ Q.zeroIso.symm)
    (hstep : ∀ a, (P.step a).hom ≫ (s (a + 1)).hom =
      tensorHom e.hom (s a).hom ≫ (Q.step a).hom) (a : ℤ) : s a = iso P Q e a := by
  refine int_induction_of_iff (P := fun a ↦ s a = iso P Q e a) ?_ ?_ a
  · exact hzero
  · intro a
    constructor
    · intro h
      apply Iso.ext
      rw [← cancel_epi (P.step a).hom, hstep, iso_step, h]
    · intro h
      apply Iso.ext
      have hh : tensorHom e.hom (s a).hom = tensorHom e.hom (iso P Q e a).hom := by
        rw [← cancel_mono (Q.step a).hom, ← hstep, ← iso_step, h]
      simp only [tensorHom_def, cancel_epi] at hh
      exact (Q.tensorInverse 1).whiskerLeft_injective hh

/-- A multiplicative comparison is determined by its value at one. -/
theorem iso_unique (s : ∀ a, P.obj a ≅ Q.obj a)
    (hzero : (s 0).hom ≫ Q.zeroIso.hom = P.zeroIso.hom)
    (hone : s 1 = e)
    (hmul : ∀ a b, (P.addIso a b).hom ≫ (s (a + b)).hom =
      tensorHom (s a).hom (s b).hom ≫ (Q.addIso a b).hom) (a : ℤ) :
    s a = iso P Q e a := by
  apply iso_unique_of_step P Q e s
  · apply Iso.ext
    rw [← cancel_mono Q.zeroIso.hom]
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hzero
  · intro b
    dsimp only [step, mulIso, Iso.trans_hom, eqToIso.hom]
    rw [Category.assoc, ← iso_naturality P Q s (add_comm 1 b),
      ← Category.assoc, hmul, hone, Category.assoc]

/-- Multiplicativity and degree one determine the entire isomorphism. -/
theorem iso_unique_mul (s : ∀ a, P.obj a ≅ Q.obj a) (hone : s 1 = e)
    (hmul : ∀ a b, (P.addIso a b).hom ≫ (s (a + b)).hom =
      tensorHom (s a).hom (s b).hom ≫ (Q.addIso a b).hom) (a : ℤ) :
    s a = iso P Q e a := by
  have hzero : s 0 = iso P Q e 0 := by
    have hs := hmul 1 0
    have ht := iso_mul P Q e 1 0 (1 + 0) rfl
    simp only [mulIso_rfl, hone, iso_one] at hs ht
    have hh : tensorHom e.hom (s 0).hom = tensorHom e.hom (iso P Q e 0).hom := by
      rw [← cancel_mono (Q.addIso 1 0).hom, ← hs, ← ht]
      change (P.addIso 1 0).hom ≫ (s 1).hom =
        (P.addIso 1 0).hom ≫ (iso P Q e 1).hom
      rw [hone, iso_one]
    apply Iso.ext
    simp only [tensorHom_def, cancel_epi] at hh
    exact (Q.tensorInverse 1).whiskerLeft_injective hh
  apply iso_unique P Q e s _ hone hmul a
  rw [hzero, iso_zero]
  simp

/-- The family constantly equal to the tensor unit. -/
abbrev constant : IntTensorFamily C where
  obj _ := 𝟙_ C
  zeroIso := Iso.refl _
  addIso _ _ := λ_ _
  zero_left _ := by simp
  zero_right _ := by simp [unitors_equal]
  assoc _ _ _ := by simp only [eqToHom_refl, Category.comp_id]; monoidal

/-- An integer family whose degree-one object is the unit has commutative multiplication. -/
theorem braiding_mul_of_one_iso [BraidedCategory C] (h : P.obj 1 ≅ 𝟙_ C) (a b : ℤ) :
    (β_ (P.obj a) (P.obj b)).hom ≫ (P.addIso b a).hom ≫
      eqToHom (congrArg P.obj (add_comm b a)) = (P.addIso a b).hom := by
  let Q : IntTensorFamily C := constant
  let s := iso P Q h
  have hs := iso_mul P Q h a b (a + b) rfl
  have ht := iso_mul P Q h b a (b + a) rfl
  simp only [mulIso_rfl] at hs ht
  rw [← cancel_mono (s (a + b)).hom]
  simp only [Category.assoc]
  rw [← iso_naturality P Q s (add_comm b a), reassoc_of% ht, hs]
  have hh : eqToHom (congrArg Q.obj (add_comm b a)) = 𝟙 (𝟙_ C) := rfl
  rw [hh, Category.comp_id, ← BraidedCategory.braiding_naturality_assoc]
  change tensorHom (s a).hom (s b).hom ≫ (β_ (𝟙_ C) (𝟙_ C)).hom ≫
    (λ_ (𝟙_ C)).hom = tensorHom (s a).hom (s b).hom ≫ (λ_ (𝟙_ C)).hom
  rw [braiding_leftUnitor]
  exact congrArg (fun f ↦ tensorHom (s a).hom (s b).hom ≫ f) unitors_equal.symm

variable {D : Type*} [Category* D] [MonoidalCategory D]

/-- A multiplicative comparison with the image under a monoidal functor. -/
theorem map_iso_mul (F : C ⥤ D) [F.Monoidal] (Q : IntTensorFamily D)
    (h : F.obj (P.obj 1) ≅ Q.obj 1) (a b : ℤ) :
    F.map (P.addIso a b).hom ≫ (iso (P.map F) Q h (a + b)).hom =
      Functor.OplaxMonoidal.δ F (P.obj a) (P.obj b) ≫
        tensorHom (iso (P.map F) Q h a).hom (iso (P.map F) Q h b).hom ≫
          (Q.addIso a b).hom := by
  have H := iso_mul (P.map F) Q h a b (a + b) rfl
  rw [mulIso_rfl, mulIso_rfl] at H
  rw [← cancel_epi (inv (Functor.OplaxMonoidal.δ F (P.obj a) (P.obj b)))]
  simpa only [map, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    Category.assoc, IsIso.inv_hom_id_assoc] using H

/-- Multiplicative inverse-image comparisons are determined in degree one. -/
theorem map_iso_unique_mul (F : C ⥤ D) [F.Monoidal] (Q : IntTensorFamily D)
    (h : F.obj (P.obj 1) ≅ Q.obj 1) (s : ∀ a, F.obj (P.obj a) ≅ Q.obj a)
    (hone : s 1 = h)
    (hmul : ∀ a b, F.map (P.addIso a b).hom ≫ (s (a + b)).hom =
      Functor.OplaxMonoidal.δ F (P.obj a) (P.obj b) ≫
        tensorHom (s a).hom (s b).hom ≫ (Q.addIso a b).hom) (a : ℤ) :
    s a = iso (P.map F) Q h a := by
  apply iso_unique_mul (P.map F) Q h s hone
  intro b c
  rw [← cancel_epi (Functor.OplaxMonoidal.δ F (P.obj b) (P.obj c))]
  simpa only [map, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    ← Category.assoc, IsIso.hom_inv_id, Category.id_comp] using hmul b c

/-- Multiplication with an explicitly identified resulting degree commutes with pullback. -/
theorem map_iso_mul_eq (F : C ⥤ D) [F.Monoidal] (Q : IntTensorFamily D)
    (h : F.obj (P.obj 1) ≅ Q.obj 1) (a b c : ℤ) (hc : a + b = c) :
    F.map (P.mulIso a b c hc).hom ≫ (iso (P.map F) Q h c).hom =
      Functor.OplaxMonoidal.δ F (P.obj a) (P.obj b) ≫
        tensorHom (iso (P.map F) Q h a).hom (iso (P.map F) Q h b).hom ≫
          (Q.mulIso a b c hc).hom := by
  subst hc
  simpa only [mulIso_rfl] using map_iso_mul P F Q h a b

/-- The pullback comparison at zero is its monoidal unit comparison. -/
theorem map_iso_zero (F : C ⥤ D) [F.Monoidal] (Q : IntTensorFamily D)
    (h : F.obj (P.obj 1) ≅ Q.obj 1) :
    (iso (P.map F) Q h 0).hom ≫ Q.zeroIso.hom =
      F.map P.zeroIso.hom ≫ Functor.OplaxMonoidal.η F := by
  simp only [iso_zero, map, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Composition
variable {E : Type*} [Category* E] [MonoidalCategory E]

/-- Multiplicative comparisons compose through an oplax-compatible natural isomorphism. -/
theorem comparison_comp_mul (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (Q : IntTensorFamily D) (R : IntTensorFamily E) (k : H ≅ F ⋙ G)
    (hk : ∀ X Y, Functor.OplaxMonoidal.δ H X Y ≫
      tensorHom (k.hom.app X) (k.hom.app Y) = k.hom.app (X ⊗ Y) ≫
        G.map (Functor.OplaxMonoidal.δ F X Y) ≫ Functor.OplaxMonoidal.δ G _ _)
    (s : ∀ a, F.obj (P.obj a) ≅ Q.obj a)
    (t : ∀ a, G.obj (Q.obj a) ≅ R.obj a)
    (hs : ∀ a b, F.map (P.addIso a b).hom ≫ (s (a + b)).hom =
      Functor.OplaxMonoidal.δ F _ _ ≫ tensorHom (s a).hom (s b).hom ≫
        (Q.addIso a b).hom)
    (ht : ∀ a b, G.map (Q.addIso a b).hom ≫ (t (a + b)).hom =
      Functor.OplaxMonoidal.δ G _ _ ≫ tensorHom (t a).hom (t b).hom ≫
        (R.addIso a b).hom) (a b : ℤ) :
    H.map (P.addIso a b).hom ≫
      (k.app (P.obj (a + b)) ≪≫ G.mapIso (s (a + b)) ≪≫ t (a + b)).hom =
    Functor.OplaxMonoidal.δ H _ _ ≫
      tensorHom (k.app (P.obj a) ≪≫ G.mapIso (s a) ≪≫ t a).hom
        (k.app (P.obj b) ≪≫ G.mapIso (s b) ≪≫ t b).hom ≫ (R.addIso a b).hom := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [k.hom.naturality_assoc]
  change k.hom.app _ ≫ G.map (F.map (P.addIso a b).hom) ≫ _ = _
  rw [← G.map_comp_assoc, hs, G.map_comp, G.map_comp, Category.assoc, Category.assoc,
    ht]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc]
  rw [reassoc_of% (hk (P.obj a) (P.obj b)).symm]
  simp only [← tensorHom_comp_tensorHom_assoc]

end Composition

/-- A faithful braided monoidal functor detects commutativity of an integer family. -/
theorem braiding_mul_of_map [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] [F.Faithful]
    (h : F.obj (P.obj 1) ≅ 𝟙_ D) (a b : ℤ) :
    (β_ (P.obj a) (P.obj b)).hom ≫ (P.addIso b a).hom ≫
      eqToHom (congrArg P.obj (add_comm b a)) = (P.addIso a b).hom := by
  have H := braiding_mul_of_one_iso (P.map F) h a b
  apply F.map_injective
  rw [← cancel_epi (inv (Functor.OplaxMonoidal.δ F (P.obj a) (P.obj b)))]
  simp only [map, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    Functor.map_comp, eqToHom_map, Category.assoc] at H ⊢
  have hb : (β_ (F.obj (P.obj a)) (F.obj (P.obj b))).hom ≫
      inv (Functor.OplaxMonoidal.δ F (P.obj b) (P.obj a)) =
      inv (Functor.OplaxMonoidal.δ F (P.obj a) (P.obj b)) ≫
        F.map (β_ (P.obj a) (P.obj b)).hom := by
    have hi (X Y : C) : inv (Functor.OplaxMonoidal.δ F X Y) =
        Functor.LaxMonoidal.μ F X Y :=
      IsIso.inv_eq_of_hom_inv_id (Functor.Monoidal.δ_μ F X Y)
    simp only [hi]
    exact
      (Functor.Braided.braided (F := F) (P.obj a) (P.obj b)).symm
  rw [reassoc_of% hb] at H
  exact H

end CategoryTheory.MonoidalCategory.IntTensorFamily
