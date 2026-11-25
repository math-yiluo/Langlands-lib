/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Artin–Schreier extensions given by a reciprocal polynomial

Let `k₀` be a finite field with `q` elements, `K` a field containing `k₀` and `b ∈ K` nonzero.
The roots of the Artin–Schreier polynomial `Xᵠ - X - b` are the inverses of the roots of the
*reciprocal polynomial* `Xᵠ + b⁻¹ Xᵠ⁻¹ - b⁻¹` (`ArtinSchreier.reciprocalPoly`). When the latter
is irreducible, adjoining one of its roots gives a field `K'` containing a solution `u` of
`uᵠ - u = b` (`ArtinSchreier.root_pow_card_sub_root`), and the translations `u ↦ u + d`,
`d ∈ k₀`, are `K`-algebra endomorphisms of `K'` (`ArtinSchreier.translation`), the Frobenius
`x ↦ xᵠ` being additive and fixing `k₀`.

The reciprocal polynomial is used because its irreducibility is the Eisenstein criterion when
`b` has a simple pole (`Polynomial.irreducible_map_X_pow_add_C_mul_X_pow_sub_C`).
-/

@[expose] public section

open Polynomial

namespace ArtinSchreier

variable (k₀ : Type*) [Field k₀] [Fintype k₀] {K : Type*} [Field K] [Algebra k₀ K]

/-- The reciprocal `Xᵠ + b⁻¹ Xᵠ⁻¹ - b⁻¹` of the Artin–Schreier polynomial `Xᵠ - X - b`,
`q = #k₀`: its roots are the inverses of the roots of `Xᵠ - X - b`. -/
noncomputable def reciprocalPoly (b : K) : K[X] :=
  X ^ Fintype.card k₀ + (C b⁻¹ * X ^ (Fintype.card k₀ - 1) - C b⁻¹)

variable (b : K) [Fact (Irreducible (reciprocalPoly k₀ b))]

/-- The field obtained by adjoining a root of the reciprocal Artin–Schreier polynomial. -/
abbrev Extension : Type _ := AdjoinRoot (reciprocalPoly k₀ b)

/-- The solution `u` of `uᵠ - u = b` in `ArtinSchreier.Extension k₀ b`: the inverse of the
adjoined root of the reciprocal polynomial. -/
noncomputable def root : Extension k₀ b := (AdjoinRoot.root (reciprocalPoly k₀ b))⁻¹

omit [Algebra k₀ K] in
lemma two_le_card : 2 ≤ Fintype.card k₀ := Fintype.one_lt_card

omit [Algebra k₀ K] in
lemma exists_card_eq_add_one : ∃ m, Fintype.card k₀ = m + 1 :=
  ⟨_, (Nat.sub_one_add_one (by have := two_le_card k₀; omega)).symm⟩

variable {k₀ b}

omit [Field k₀] [Algebra k₀ K] [Fact (Irreducible (reciprocalPoly k₀ b))] in
lemma eval₂_reciprocalPoly {L : Type*} [CommRing L] (f : K →+* L) (x : L) :
    (reciprocalPoly k₀ b).eval₂ f x =
      x ^ Fintype.card k₀ + (f b⁻¹ * x ^ (Fintype.card k₀ - 1) - f b⁻¹) := by
  simp [reciprocalPoly]

omit [Fact (Irreducible (reciprocalPoly k₀ b))] in
omit [Algebra k₀ K] in
/-- An element `v ≠ 0` with `vᵠ - v = b` is the inverse of a root of the reciprocal
polynomial. -/
lemma eval₂_inv_reciprocalPoly {L : Type*} [Field L] (f : K →+* L) (hb : b ≠ 0) {v : L}
    (hv : v ≠ 0) (h : v ^ Fintype.card k₀ - v = f b) :
    (reciprocalPoly k₀ b).eval₂ f v⁻¹ = 0 := by
  obtain ⟨m, hm⟩ := exists_card_eq_add_one k₀
  have hfb : f b ≠ 0 := (map_ne_zero f).2 hb
  rw [eval₂_reciprocalPoly, hm, Nat.add_sub_cancel, map_inv₀]
  rw [hm] at h
  have key : f b * v ^ (m + 1) * ((v⁻¹) ^ (m + 1) + ((f b)⁻¹ * (v⁻¹) ^ m - (f b)⁻¹)) =
      f b + v - v ^ (m + 1) := by
    rw [inv_pow, inv_pow]
    field_simp
    ring
  have h0 : f b + v - v ^ (m + 1) = 0 := by linear_combination -h
  rw [h0] at key
  simpa [hfb, hv] using key

omit [Algebra k₀ K] in
lemma root_ne_zero (hb : b ≠ 0) : root k₀ b ≠ 0 := by
  have h1 := AdjoinRoot.eval₂_root (reciprocalPoly k₀ b)
  obtain ⟨m, hm⟩ := exists_card_eq_add_one k₀
  have : m ≠ 0 := by have := two_le_card k₀; omega
  rw [eval₂_reciprocalPoly, hm, Nat.add_sub_cancel] at h1
  refine inv_ne_zero fun h ↦ hb ?_
  rw [h, zero_pow (Nat.succ_ne_zero m), zero_pow this, mul_zero, zero_add, zero_sub,
    neg_eq_zero, map_inv₀, inv_eq_zero] at h1
  exact (map_eq_zero_iff _ (AdjoinRoot.of (reciprocalPoly k₀ b)).injective).1 h1

omit [Algebra k₀ K] in
/-- The root `u` satisfies the Artin–Schreier equation `uᵠ - u = b`. -/
lemma root_pow_card_sub_root (hb : b ≠ 0) :
    root k₀ b ^ Fintype.card k₀ - root k₀ b = algebraMap K (Extension k₀ b) b := by
  have hw : AdjoinRoot.root (reciprocalPoly k₀ b) ≠ 0 :=
    fun h ↦ root_ne_zero hb (by rw [root, h, inv_zero])
  have h1 := AdjoinRoot.eval₂_root (reciprocalPoly k₀ b)
  obtain ⟨m, hm⟩ := exists_card_eq_add_one k₀
  rw [eval₂_reciprocalPoly, hm, Nat.add_sub_cancel, map_inv₀] at h1
  have hb' : AdjoinRoot.of (reciprocalPoly k₀ b) b ≠ 0 :=
    (map_ne_zero (AdjoinRoot.of (reciprocalPoly k₀ b))).2 hb
  rw [AdjoinRoot.algebraMap_eq, root, hm]
  set w := AdjoinRoot.root (reciprocalPoly k₀ b)
  set β := AdjoinRoot.of (reciprocalPoly k₀ b) b
  have key : β * (w⁻¹) ^ (m + 1) * (w ^ (m + 1) + (β⁻¹ * w ^ m - β⁻¹)) =
      β + w⁻¹ - (w⁻¹) ^ (m + 1) := by
    rw [inv_pow]
    field_simp
    ring
  rw [h1, mul_zero] at key
  linear_combination key


lemma root_add_pow_card_sub (hb : b ≠ 0) (d : k₀) :
    (root k₀ b + algebraMap k₀ (Extension k₀ b) d) ^ Fintype.card k₀ -
      (root k₀ b + algebraMap k₀ (Extension k₀ b) d) = algebraMap K (Extension k₀ b) b := by
  have hadd : (root k₀ b + algebraMap k₀ (Extension k₀ b) d) ^ Fintype.card k₀ =
      root k₀ b ^ Fintype.card k₀ + algebraMap k₀ (Extension k₀ b) d := by
    simpa using map_add (FiniteField.frobeniusAlgHom k₀ (Extension k₀ b)) (root k₀ b)
      (algebraMap k₀ _ d)
  rw [hadd, ← root_pow_card_sub_root hb]
  ring

/-- The translation `u ↦ u + d` of the Artin–Schreier root by `d ∈ k₀`, a `K`-algebra
endomorphism of `ArtinSchreier.Extension k₀ b`: `u + d` is again a solution of `vᵠ - v = b`. -/
noncomputable def translation (hb : b ≠ 0) (d : k₀) : Extension k₀ b →ₐ[K] Extension k₀ b :=
  AdjoinRoot.liftAlgHom (reciprocalPoly k₀ b) (Algebra.ofId K (Extension k₀ b))
    (root k₀ b + algebraMap k₀ (Extension k₀ b) d)⁻¹ <| by
    refine eval₂_inv_reciprocalPoly _ hb (fun h ↦ hb ?_) (root_add_pow_card_sub hb d)
    have := root_add_pow_card_sub hb d
    rw [h, zero_pow (by have := two_le_card k₀; omega), sub_zero] at this
    exact (map_eq_zero_iff _ (algebraMap K (Extension k₀ b)).injective).1 this.symm

/-- The translation by `d` moves the Artin–Schreier root `u` to `u + d`. -/
lemma translation_root (hb : b ≠ 0) (d : k₀) :
    translation hb d (root k₀ b) = root k₀ b + algebraMap k₀ (Extension k₀ b) d := by
  conv_lhs => rw [root]
  rw [map_inv₀, translation, AdjoinRoot.liftAlgHom_root, inv_inv]

end ArtinSchreier

