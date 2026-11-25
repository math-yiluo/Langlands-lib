/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.AdjoinRootCover
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Algebra

/-! # Translations of the Artin–Schreier cover

For a scheme `S` with `p = 0` on `S` and `f ∈ Γ(S, ⊤)`, the cover
`adjoinRootCover S (T ^ p - T - f)` carries the translations `T ↦ T + a`, `a ∈ 𝔽_p`, which
preserve the equation since `a ^ p = a`; the inverse of `T ↦ T + a` is `T ↦ T - a`.
Source: blueprint, lemma-artin-schreier-character-sheaf, step (3);
lem-sc-field-artin-schreier-kernel.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

section ZModCast

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]

/-- In a ring where the prime `p` vanishes, the cast of the representative of `a : ZMod p` is
the image of `a` under the canonical ring map. -/
lemma natCast_val_eq_zmodRingHomOfNatCastEqZero (h : (p : A) = 0) (a : ZMod p) :
    ((a.val : ℕ) : A) = zmodRingHomOfNatCastEqZero p h a := by
  rw [← map_natCast (zmodRingHomOfNatCastEqZero p h), ZMod.natCast_zmod_val]

/-- The cast of the representative is additive in characteristic `p`. -/
lemma natCast_val_add_of_natCast_eq_zero (h : (p : A) = 0) (a b : ZMod p) :
    (((a + b).val : ℕ) : A) = (a.val : A) + (b.val : A) := by
  simp only [natCast_val_eq_zmodRingHomOfNatCastEqZero h, map_add]

/-- Elements of the prime field are fixed by Frobenius. -/
lemma natCast_val_pow_of_natCast_eq_zero (h : (p : A) = 0) (a : ZMod p) :
    ((a.val : ℕ) : A) ^ p = (a.val : A) := by
  rw [natCast_val_eq_zmodRingHomOfNatCastEqZero h, ← map_pow, ZMod.pow_card]

/-- Translating a solution of `t ^ p - t = c` by an element of the prime field gives another
solution. -/
lemma add_natCast_val_pow_sub (h : (p : A) = 0) {t c : A} (ht : t ^ p - t = c) (a : ZMod p) :
    (t + (a.val : A)) ^ p - (t + (a.val : A)) - c = 0 := by
  rw [add_pow_prime_of_natCast_eq_zero p h, natCast_val_pow_of_natCast_eq_zero h, ← ht]
  ring

end ZModCast

variable (p : ℕ) (S : Scheme.{u}) (f : Γ(S, ⊤))

/-- The Artin–Schreier polynomial `T ^ p - T - f` is monic. -/
lemma monic_artinSchreier [Fact p.Prime] : (X ^ p - X - C f : Polynomial Γ(S, ⊤)).Monic := by
  rw [sub_sub]
  refine monic_X_pow_sub ?_
  refine (degree_add_le _ _).trans_lt ?_
  refine max_lt (degree_X_le.trans_lt ?_) ((degree_C_le).trans_lt ?_)
  · exact_mod_cast (Fact.out : p.Prime).one_lt
  · exact_mod_cast (Fact.out : p.Prime).pos

/-- The Artin–Schreier polynomial `T ^ p - T - f` has degree `p`. -/
lemma natDegree_artinSchreier [Fact p.Prime] [Nontrivial Γ(S, ⊤)] :
    (X ^ p - X - C f : Polynomial Γ(S, ⊤)).natDegree = p := by
  rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  refine (natDegree_add_le _ _).trans_lt ?_
  rw [natDegree_X, natDegree_C, max_eq_left (Nat.zero_le 1)]
  exact (Fact.out : p.Prime).one_lt

/-- In characteristic `p`, the derivative of `T ^ p - T - f` is `-1`. -/
lemma derivative_artinSchreier (hchar : (p : Γ(S, ⊤)) = 0) :
    derivative (X ^ p - X - C f : Polynomial Γ(S, ⊤)) = -1 := by
  simp [derivative_X_pow, hchar]

/-- The root condition for the Artin–Schreier polynomial. -/
lemma eval₂_artinSchreier {A : Type*} [CommRing A] (φ : Γ(S, ⊤) →+* A) (t : A) :
    (X ^ p - X - C f : Polynomial Γ(S, ⊤)).eval₂ φ t = t ^ p - t - φ f := by
  simp

variable {p S f} {P : Polynomial Γ(S, ⊤)}

/-- The root condition for a polynomial equal to the Artin–Schreier polynomial. -/
lemma eval₂_of_eq_artinSchreier (hP : P = X ^ p - X - C f) {A : Type*} [CommRing A]
    (φ : Γ(S, ⊤) →+* A) (t : A) : P.eval₂ φ t = t ^ p - t - φ f := by
  rw [hP, eval₂_artinSchreier]

/-- The class of `T` on the Artin–Schreier cover satisfies `T ^ p - T = f`. -/
lemma adjoinRootCoverRoot_pow_sub (hP : P = X ^ p - X - C f) :
    adjoinRootCoverRoot S P ^ p - adjoinRootCoverRoot S P =
      (adjoinRootCover S P).hom.appTop f := by
  have h := eval₂_adjoinRootCoverRoot S P
  rw [eval₂_of_eq_artinSchreier hP] at h
  exact sub_eq_zero.mp h

/-- `p` vanishes on every scheme over `S` if it vanishes on `S`. -/
lemma natCast_appTop_eq_zero (hchar : (p : Γ(S, ⊤)) = 0) {Z : Scheme.{u}} (g : Z ⟶ S) :
    (p : Γ(Z, ⊤)) = 0 := by
  rw [← map_natCast g.appTop.hom, hchar, map_zero]

variable [Fact p.Prime]

/-- The translation `T ↦ T + a` of the Artin–Schreier cover. -/
def artinSchreierTranslation (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0)
    (a : ZMod p) : (adjoinRootCover S P).left ⟶ (adjoinRootCover S P).left :=
  adjoinRootCoverLift (adjoinRootCover S P).hom
    (adjoinRootCoverRoot S P + (a.val : Γ((adjoinRootCover S P).left, ⊤))) (by
      rw [eval₂_of_eq_artinSchreier hP]
      exact add_natCast_val_pow_sub (natCast_appTop_eq_zero hchar (adjoinRootCover S P).hom)
        (adjoinRootCoverRoot_pow_sub hP) a)

@[reassoc (attr := simp)]
lemma artinSchreierTranslation_hom (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0)
    (a : ZMod p) :
    artinSchreierTranslation hP hchar a ≫ (adjoinRootCover S P).hom = (adjoinRootCover S P).hom :=
  adjoinRootCoverLift_hom _ _ _

lemma artinSchreierTranslation_appTop_root (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) (a : ZMod p) :
    (artinSchreierTranslation hP hchar a).appTop (adjoinRootCoverRoot S P) =
      adjoinRootCoverRoot S P + (a.val : Γ((adjoinRootCover S P).left, ⊤)) :=
  adjoinRootCoverLift_appTop_root _ _ _

/-- Composing a morphism into the cover with a translation adds `a` to the pulled back
coordinate. -/
lemma comp_artinSchreierTranslation_appTop_root (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) (a : ZMod p) {Z : Scheme.{u}}
    (s : Z ⟶ (adjoinRootCover S P).left) :
    (s ≫ artinSchreierTranslation hP hchar a).appTop (adjoinRootCoverRoot S P) =
      s.appTop (adjoinRootCoverRoot S P) + (a.val : Γ(Z, ⊤)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, artinSchreierTranslation_appTop_root,
    map_add, map_natCast]

lemma artinSchreierTranslation_zero (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0) :
    artinSchreierTranslation hP hchar 0 = 𝟙 _ := by
  refine adjoinRootCover_hom_ext (by simp) ?_
  rw [artinSchreierTranslation_appTop_root]
  simp

lemma artinSchreierTranslation_add (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0)
    (a b : ZMod p) :
    artinSchreierTranslation hP hchar (a + b) =
      artinSchreierTranslation hP hchar a ≫ artinSchreierTranslation hP hchar b := by
  refine adjoinRootCover_hom_ext (by simp) ?_
  rw [comp_artinSchreierTranslation_appTop_root, artinSchreierTranslation_appTop_root,
    artinSchreierTranslation_appTop_root, natCast_val_add_of_natCast_eq_zero
      (natCast_appTop_eq_zero hchar (adjoinRootCover S P).hom)]
  ring

/-- The translation by `a`, as an automorphism of the Artin–Schreier cover over `S`. -/
def artinSchreierTranslationIso (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0)
    (a : ZMod p) : Aut (adjoinRootCover S P) :=
  .of <| Over.isoMk
    { hom := artinSchreierTranslation hP hchar a
      inv := artinSchreierTranslation hP hchar (-a)
      hom_inv_id := by
        rw [← artinSchreierTranslation_add, add_neg_cancel, artinSchreierTranslation_zero]
      inv_hom_id := by
        rw [← artinSchreierTranslation_add, neg_add_cancel, artinSchreierTranslation_zero] }
    (artinSchreierTranslation_hom hP hchar a)

@[simp]
lemma artinSchreierTranslationIso_hom_left (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) (a : ZMod p) :
    (artinSchreierTranslationIso hP hchar a).asIso.hom.left = artinSchreierTranslation hP hchar a :=
  rfl

/-- The translation action of `𝔽_p` on the Artin–Schreier cover. -/
def artinSchreierAction (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0) :
    Multiplicative (ZMod p) →* Aut (adjoinRootCover S P) where
  toFun a := artinSchreierTranslationIso hP hchar a.toAdd
  map_one' := by
    apply Aut.ext
    rw [Aut.one_asIso]
    ext : 1
    refine Over.OverMorphism.ext ?_
    exact artinSchreierTranslation_zero hP hchar
  map_mul' a b := by
    apply Aut.ext
    rw [Aut.mul_asIso]
    ext : 1
    refine Over.OverMorphism.ext ?_
    exact (congr_arg (artinSchreierTranslation hP hchar) (add_comm a.toAdd b.toAdd)).trans
      (artinSchreierTranslation_add hP hchar _ _)

@[simp]
lemma artinSchreierAction_hom_left (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0)
    (a : ZMod p) :
    (artinSchreierAction hP hchar (Multiplicative.ofAdd a)).asIso.hom.left =
      artinSchreierTranslation hP hchar a :=
  rfl

end AlgebraicGeometry
