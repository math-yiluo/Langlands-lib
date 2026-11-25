/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily

/-!
# Normalized signed powers of an invertible line

Source: Stacks Project, Modules on Sites, Sections 03EK and 04TT; the integer-power
construction in `WeilConjectures.CategoryTheory.Monoidal.TensorInverse`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
namespace CategoryTheory.MonoidalCategory.NormalizedSignedPowers

local instance : MonoidalCategory (Discrete ℤ) := Discrete.addMonoidal ℤ

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

noncomputable def inversePower {L : C} (e : TensorInverse L) (a : ℤ) :
    TensorInverse (e.zpow a) where
  obj := e.zpow (-a)
  rightIso := e.addIso a (-a) 0 (add_neg_cancel a)
  leftIso := e.addIso (-a) a 0 (neg_add_cancel a)

lemma curry_iso_of_inverse {X Y Z : C} (e : TensorInverse X) (b : X ⊗ Y ≅ Z) :
    IsIso (MonoidalClosed.curry b.hom) := by
  let E := e.tensorLeftEquivalence
  have : (tensorLeft X).Full := E.fullyFaithfulFunctor.full
  have : (tensorLeft X).Faithful := E.fullyFaithfulFunctor.faithful
  rw [MonoidalClosed.curry_eq]
  have : IsIso ((ihom.coev X).app Y) :=
    inferInstanceAs (IsIso ((ihom.adjunction X).unit.app Y))
  infer_instance

noncomputable def positivePowerIso
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) :
    (n : ℕ) → e.zpow (.ofNat n) ≅ P n
  | 0 => eqToIso h0.symm
  | 1 => ρ_ _
  | n + 2 => (e.addIso (.ofNat (n + 1)) 1 (.ofNat (n + 2)) rfl).symm ≪≫
    tensorIso (positivePowerIso P h0 hs e (n + 1)) (ρ_ _) ≪≫ eqToIso (hs n).symm

noncomputable def dualPowerPairing
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) (n : ℕ) :
    P (n + 1) ⊗ e.zpow (.negSucc n) ≅ P 0 :=
  tensorIso (positivePowerIso P h0 hs e (n + 1)).symm (Iso.refl _) ≪≫
    e.addIso (.ofNat (n + 1)) (.negSucc n) 0 (by
      simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega) ≪≫ eqToIso h0.symm

noncomputable def inversePositivePower
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) (n : ℕ) :
    TensorInverse (P n) where
  obj := e.zpow (-Int.ofNat n)
  rightIso := tensorIso (positivePowerIso P h0 hs e n).symm (Iso.refl _) ≪≫
    (inversePower e (.ofNat n)).rightIso
  leftIso := tensorIso (Iso.refl _) (positivePowerIso P h0 hs e n).symm ≪≫
    (inversePower e (.ofNat n)).leftIso

noncomputable def dualPowerIso
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) (n : ℕ) :
    e.zpow (.negSucc n) ≅ (ihom (P (n + 1))).obj (P 0) :=
  have := curry_iso_of_inverse (inversePositivePower P h0 hs e (n + 1))
    (dualPowerPairing P h0 hs e n)
  asIso (MonoidalClosed.curry (dualPowerPairing P h0 hs e n).hom)

noncomputable def signedPower (P : ℕ → C) : ℤ → C
  | .ofNat n => P n
  | .negSucc n => (ihom (P (n + 1))).obj (P 0)

noncomputable def signedPowerIso
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) :
    (a : ℤ) → e.zpow a ≅ signedPower P a
  | .ofNat n => positivePowerIso P h0 hs e n
  | .negSucc n => dualPowerIso P h0 hs e n

omit [MonoidalCategory C] [MonoidalClosed C] in
lemma discrete_functor_map (P : ℤ → C) {a b : Discrete ℤ} (f : a ⟶ b) :
    (Discrete.functor P).map f = eqToHom (congrArg P (Discrete.eq_of_hom f)) := by
  cases a
  cases b
  cases f
  rfl

noncomputable def signedFamily
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) :
    IntTensorFamily C := by
  have hu : (𝟙_ (Discrete ℤ)) = Discrete.mk (0 : ℤ) := rfl
  have ht (a b : ℤ) : (Discrete.mk a ⊗ Discrete.mk b) = Discrete.mk (a + b) := rfl
  let q := signedPowerIso P h0 hs e
  let F := Discrete.functor (signedPower P)
  let i : e.intTensorFamily.toFunctor ≅ F :=
    Discrete.natIso (fun a ↦ q a.as)
  let : F.Monoidal := Functor.Monoidal.transport i
  exact {
    obj := signedPower P
    zeroIso := (Functor.Monoidal.εIso F).symm
    addIso a b := Functor.Monoidal.μIso F ⟨a⟩ ⟨b⟩
    zero_left := by
      intro a
      rw [← cancel_epi ((Functor.LaxMonoidal.ε F) ▷ F.obj ⟨a⟩)]
      have h := Functor.LaxMonoidal.left_unitality F ⟨a⟩
      convert h using 1 <;>
        simp [F, discrete_functor_map]
      all_goals rfl
    zero_right := by
      intro a
      rw [← cancel_epi (F.obj ⟨a⟩ ◁ (Functor.LaxMonoidal.ε F))]
      have h := Functor.LaxMonoidal.right_unitality F ⟨a⟩
      convert h using 1 <;>
        simp [F, discrete_functor_map]
      all_goals rfl
    assoc := by
      intro a b c
      rw [← cancel_mono (eqToHom (congrArg (signedPower P) (add_assoc a b c)))]
      have h := Functor.LaxMonoidal.associativity F ⟨a⟩ ⟨b⟩ ⟨c⟩
      convert h using 1 <;>
        simp [F, discrete_functor_map]
      all_goals rfl }

lemma signedFamily_addIso
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) (a b : ℤ) :
    (signedFamily P h0 hs e).addIso a b =
      tensorIso (signedPowerIso P h0 hs e a).symm (signedPowerIso P h0 hs e b).symm ≪≫
        e.addIso a b (a + b) rfl ≪≫ signedPowerIso P h0 hs e (a + b) := by
  apply Iso.ext
  rfl

lemma signedFamily_zeroIso
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) :
    (signedFamily P h0 hs e).zeroIso = eqToIso h0 := by
  apply Iso.ext
  change (signedPowerIso P h0 hs e 0).inv ≫ 𝟙 _ = _
  simp [signedPowerIso, positivePowerIso]

lemma signedFamily_positive_one
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) (n : ℕ) :
    (signedFamily P h0 hs e).addIso (.ofNat (n + 1)) 1 = eqToIso (hs n).symm := by
  rw [signedFamily_addIso]
  change tensorIso (positivePowerIso P h0 hs e (n + 1)).symm (ρ_ _).symm ≪≫
    e.addIso (.ofNat (n + 1)) 1 (.ofNat (n + 2)) rfl ≪≫
      ((e.addIso (.ofNat (n + 1)) 1 (.ofNat (n + 2)) rfl).symm ≪≫
        tensorIso (positivePowerIso P h0 hs e (n + 1)) (ρ_ _) ≪≫ eqToIso (hs n).symm) = _
  apply Iso.ext
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
    tensorHom_id, id_whiskerRight, Category.id_comp]

/-- Pairing a positive power with its normalized negative power is evaluation.
Source: Stacks Project, Modules on Sites, Tags 03EK and 04TT.
(auxiliary; not a blueprint node).
Proof: precompose by the two signedPowerIso maps. Transported multiplication then
reduces to the integer-power pairing. The negative map is its transpose, so the
uncurry-curry identity gives evaluation, and the two positive comparison maps cancel. -/
lemma signedFamily_evaluation
    (P : ℕ → C) (h0 : P 0 = 𝟙_ C)
    (hs : ∀ n, P (n + 2) = P (n + 1) ⊗ P 1) (e : TensorInverse (P 1)) (n : ℕ) :
    ((signedFamily P h0 hs e).addIso (.ofNat (n + 1)) (.negSucc n)).hom ≫
      eqToHom (congrArg (signedPower P) (add_neg_cancel (Int.ofNat (n + 1)))) =
        (ihom.ev (P (n + 1))).app (P 0) := by
  let q := signedPowerIso P h0 hs e
  have hn {a b : ℤ} (h : a = b) :
      (q a).hom ≫ eqToHom (congrArg (signedPower P) h) =
        eqToHom (congrArg e.zpow h) ≫ (q b).hom := by
    subst b
    simp
  rw [← cancel_epi (tensorHom (q (.ofNat (n + 1))).hom (q (.negSucc n)).hom)]
  rw [signedFamily_addIso]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, Iso.hom_inv_id]
  simp only [tensorHom_id, id_whiskerRight, Category.id_comp]
  have hsum : Int.ofNat (n + 1) + Int.negSucc n = 0 := by
    simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  rw [hn hsum, ← Category.assoc, e.addIso_hom_eqToHom rfl hsum]
  change (e.addIso (.ofNat (n + 1)) (.negSucc n) 0 _).hom ≫
    (eqToIso h0.symm).hom = _
  have hc := MonoidalClosed.uncurry_curry (dualPowerPairing P h0 hs e n).hom
  rw [MonoidalClosed.uncurry_eq] at hc
  rw [tensorHom_def, Category.assoc]
  change _ = (positivePowerIso P h0 hs e (n + 1)).hom ▷ _ ≫
    P (n + 1) ◁ MonoidalClosed.curry (dualPowerPairing P h0 hs e n).hom ≫ _
  rw [hc]
  simp [dualPowerPairing]

end CategoryTheory.MonoidalCategory.NormalizedSignedPowers
