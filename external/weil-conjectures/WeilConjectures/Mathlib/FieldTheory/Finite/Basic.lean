/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.Algebra.CharP.Algebra

/-!
# The geometric Frobenius of an algebraic extension of a finite field

Mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic K L` is the *arithmetic* Frobenius
`σ : x ↦ x ^ #K` of an algebraic extension `L` of a finite field `K`, viewed as an element of
the group `Gal(L/K) = L ≃ₐ[K] L`. The *geometric* Frobenius is its inverse, and it is the
automorphism that acts on étale cohomology in the Weil conjectures.

## Main definitions

- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`: the geometric Frobenius `σ⁻¹`.

## Main statements

- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv`: the geometric Frobenius is the
  inverse of the arithmetic Frobenius. Both `σ⁻¹ * σ = 1` and `σ * σ⁻¹ = 1` follow by `simp`.
- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq`: the `m`-th power
  of the geometric Frobenius fixes the image of a field with `#K ^ m` elements.
- `FiniteField.frobeniusAlgEquivOfAlgebraic_apply_eq_self_iff`: the fixed field of the arithmetic
  Frobenius is `K`.
- `FiniteField.X_pow_card_sub_X_eq_prod`: `X ^ q - X = ∏_{c ∈ K} (X - c)`.
-/

@[expose] public section

namespace FiniteField

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Blueprint `definition-abelian-variety--1`: Finite fields, Frobenius and abelian varieties.

Fix a finite field `K` with `q` elements and an algebraic extension `L`. The *arithmetic
Frobenius* is `σ : x ↦ x ^ q`; the *geometric Frobenius* is `F = σ⁻¹`.

This is also blueprint `definition-abelian-variety--1`; its abelian varieties are
`AlgebraicGeometry.IsAbelianVariety` (see
`AlgebraicGeometry.isAbelianVariety_iff_geometricallyConnected`)
and the action of `Gal(L/K)` on geometric points by coordinates is
`AlgebraicGeometry.IsAbelianVariety.geometricPointsAddEquiv`. -/
@[simps!]
noncomputable def geometricFrobeniusAlgEquivOfAlgebraic : Gal(L/K) :=
  (frobeniusAlgEquivOfAlgebraic K L)⁻¹

@[simp]
theorem geometricFrobeniusAlgEquivOfAlgebraic_eq_inv :
    geometricFrobeniusAlgEquivOfAlgebraic K L = (frobeniusAlgEquivOfAlgebraic K L)⁻¹ :=
  rfl

/-- The `m`-th power of the geometric Frobenius of `L/K` fixes the image of any embedding of a
field `E` with `#K ^ m` elements: such a field is fixed pointwise by `x ↦ x ^ (#K ^ m)`. -/
theorem geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq {E : Type*} [Field E]
    [Finite E] (m : ℕ) (hE : Nat.card E = Fintype.card K ^ m) (ι : E →+* L) (a : E) :
    (geometricFrobeniusAlgEquivOfAlgebraic K L ^ m) (ι a) = ι a := by
  have := Fintype.ofFinite E
  rw [geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  dsimp only
  rw [← map_pow, ← hE, Nat.card_eq_fintype_card, pow_card]

/-- The ring endomorphisms of `L` commute with the powers of the geometric Frobenius, as they
commute with `x ↦ x ^ #K`. -/
theorem map_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply (β : L →+* L) (j : ℕ) (y : L) :
    β ((geometricFrobeniusAlgEquivOfAlgebraic K L ^ j) y) =
      (geometricFrobeniusAlgEquivOfAlgebraic K L ^ j) (β y) := by
  rw [geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv,
    AlgEquiv.eq_symm_apply, AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  dsimp only
  rw [← map_pow]
  congr 1
  have := AlgEquiv.apply_symm_apply (frobeniusAlgEquivOfAlgebraic K L ^ j) y
  rwa [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate] at this

open IntermediateField in
/-- Every element `y` of an algebraic extension of a finite field `K` lies in a finite
subfield, so `y ^ (#K ^ n) = y` for some `n ≥ 1`. -/
theorem exists_pow_card_pow_eq_self (y : L) : ∃ n, 1 ≤ n ∧ y ^ (Fintype.card K ^ n) = y := by
  have hy : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have : FiniteDimensional K K⟮y⟯ := IntermediateField.adjoin.finiteDimensional hy
  have : Finite K⟮y⟯ := Module.finite_of_finite K
  have := Fintype.ofFinite K⟮y⟯
  refine ⟨Module.finrank K K⟮y⟯, Module.finrank_pos, ?_⟩
  have := FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self K y⟩ : K⟮y⟯)
  rw [Module.card_eq_pow_finrank (K := K)] at this
  exact congrArg Subtype.val this

/-- A ring endomorphism of an algebraically closed algebraic extension of a finite field is
bijective: every element is a root of a polynomial `X ^ (#K ^ n) - X` with coefficients in the
image. -/
theorem bijective_ringHom_of_isAlgClosed (K' : Type*) [Field K'] [Finite K'] [Algebra K' L]
    [Algebra.IsAlgebraic K' L] [IsAlgClosed L] (β : L →+* L) : Function.Bijective β :=
  have := Fintype.ofFinite K'
  IsAlgClosed.ringHom_bijective_of_isIntegral β fun y ↦ by
    obtain ⟨n, hn, hy⟩ := exists_pow_card_pow_eq_self K' L y
    have hc : 1 < Fintype.card K' ^ n := Nat.one_lt_pow (by omega) Fintype.one_lt_card
    refine ⟨Polynomial.X ^ (Fintype.card K' ^ n) - Polynomial.X,
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hc), ?_⟩
    simp [hy]

/-- The elements of `L` fixed by the arithmetic Frobenius `x ↦ x ^ q` are exactly the elements
of `K`: every element of `K` is a root of `X ^ q - X`, and this polynomial has at most `q` roots
in `L`. -/
theorem frobeniusAlgEquivOfAlgebraic_apply_eq_self_iff {x : L} :
    frobeniusAlgEquivOfAlgebraic K L x = x ↔ x ∈ Set.range (algebraMap K L) := by
  classical
  refine ⟨fun hx ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ AlgEquiv.commutes _ a⟩
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  set f : Polynomial L := Polynomial.X ^ Fintype.card K - Polynomial.X
  have hf : f ≠ 0 := X_pow_card_sub_X_ne_zero L hq
  have hroot {y : L} : y ∈ f.roots.toFinset ↔ y ^ Fintype.card K = y := by
    simp [f, Polynomial.mem_roots hf, sub_eq_zero]
  have himage : Finset.univ.image (algebraMap K L) = f.roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
      rw [hroot, ← map_pow, pow_card]
    · rw [Finset.card_image_of_injective _ (algebraMap K L).injective, Finset.card_univ]
      calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
        _ ≤ f.natDegree := Polynomial.card_roots' f
        _ = Fintype.card K := FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  have hx' : x ∈ f.roots.toFinset := hroot.mpr hx
  rw [← himage] at hx'
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx'
  exact ⟨a, rfl⟩

/-- Two embeddings `ι, ι' : E ↪ L` of a finite field `E` which agree on a finite subfield
`K ⊆ E` differ by a power of the `#K`-power Frobenius: the `K`-embeddings of `E` into `L` are
the composites of one of them with the elements of `Gal(E/K)`, the powers of `x ↦ x ^ #K`. -/
theorem exists_apply_eq_pow_card_pow_of_comp_eq {K E L : Type*} [Field K] [Fintype K] [Field E]
    [Finite E] [Field L] (r : K →+* E) {ι ι' : E →+* L} (h : ι.comp r = ι'.comp r) :
    ∃ i : ℕ, ∀ a, ι' a = ι a ^ (Fintype.card K ^ i) := by
  let := r.toAlgebra
  let : Algebra K L := (ι.comp r).toAlgebra
  let f : E →ₐ[K] L := { ι with commutes' := fun _ ↦ rfl }
  let f' : E →ₐ[K] L := { ι' with commutes' := fun c ↦ (RingHom.congr_fun h c).symm }
  have hinj : Function.Injective
      fun n : Fin (Module.finrank K E) ↦ f.comp (frobeniusAlgHom K E ^ n.1) := by
    intro a b hab
    refine (bijective_frobeniusAlgHom_pow K E).1 (AlgHom.ext fun x ↦ f.toRingHom.injective ?_)
    exact DFunLike.congr_fun hab x
  obtain ⟨n, hn⟩ := (hinj.bijective_of_nat_card_le
    ((card_algHom_le_finrank K E L).trans_eq (by simp))).2 f'
  refine ⟨n, fun a ↦ ?_⟩
  have := DFunLike.congr_fun hn a
  simp only [AlgHom.comp_apply, AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate] at this
  exact this.symm.trans (map_pow ι _ _)

/-- An embedding `ι` of a finite field with `#K ^ n` elements, `n ≥ 1`, into an algebraic
extension `L` of `K`: on its image the `#K ^ i`-power map is a positive power of the geometric
Frobenius, the arithmetic Frobenius having order dividing `n` there. -/
theorem exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_eq {E : Type*} [Field E]
    [Finite E] {n : ℕ} (hn : 1 ≤ n) (hE : Nat.card E = Fintype.card K ^ n) (ι : E →+* L)
    (i : ℕ) : ∃ j, 1 ≤ j ∧ ∀ a,
      (geometricFrobeniusAlgEquivOfAlgebraic K L ^ j) (ι a) = ι a ^ (Fintype.card K ^ i) := by
  have := Fintype.ofFinite E
  refine ⟨n * (i + 1) - i, ?_, fun a ↦ ?_⟩
  · have : i + 1 ≤ n * (i + 1) := Nat.le_mul_of_pos_left _ hn
    omega
  rw [geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  dsimp only
  have hj : i + (n * (i + 1) - i) = n * (i + 1) := by
    have : i + 1 ≤ n * (i + 1) := Nat.le_mul_of_pos_left _ hn
    omega
  rw [← pow_mul, ← pow_add, hj, pow_mul, ← hE, Nat.card_eq_fintype_card, ← map_pow,
    FiniteField.pow_card_pow]

section ArtinSchreier

open _root_.Polynomial

variable {k A : Type*} [Field k] [Fintype k] [CommRing A]

/-- Over a finite field `k` with `q` elements, `X ^ q - X = ∏_{c ∈ k} (X - c)`. -/
theorem X_pow_card_sub_X_eq_prod : (X ^ Fintype.card k - X : k[X]) = ∏ c, (X - C c) := by
  have hq := Fintype.one_lt_card (α := k)
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hq))
    (by rw [roots_X_pow_card_sub_X, X_pow_card_sub_X_natDegree_eq k hq]; rfl),
    roots_X_pow_card_sub_X]
  rfl

/-- If `u ^ q = u` in a `k`-algebra, then `∏_{c ∈ k} (u - c) = 0`. -/
theorem prod_sub_eq_zero_of_pow_card_eq (ψ : k →+* A) {u : A} (hu : u ^ Fintype.card k = u) :
    ∏ c, (u - ψ c) = 0 := by
  have := congrArg (eval₂ ψ u) (X_pow_card_sub_X_eq_prod (k := k))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_X, hu, sub_self, eval₂_finsetProd,
    eval₂_C] at this
  exact this.symm

/-- If `x ^ q - x = y ^ q - y` in a `k`-algebra, then `(y - x) ^ q = y - x`. -/
theorem sub_pow_card_eq_of_pow_card_sub_eq (ψ : k →+* A) {x y : A}
    (h : x ^ Fintype.card k - x = y ^ Fintype.card k - y) :
    (y - x) ^ Fintype.card k = y - x := by
  obtain h' | h' := subsingleton_or_nontrivial A
  · exact Subsingleton.elim _ _
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  have := Fact.mk hp
  have := CharP.of_ringHom_of_prime ψ hp (ringChar.Nat.cast_ringChar)
  rw [hm] at h ⊢
  rw [sub_pow_char_pow]
  linear_combination -h

end ArtinSchreier

variable (k : Type*) [Field k] [Finite k]
variable (K : Type*) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-- The geometric Frobenius of an algebraic extension `K` of a finite field `k`, the
inverse of the arithmetic Frobenius `x ↦ x ^ #k`
(`FiniteField.frobeniusAlgEquivOfAlgebraic`). It is characterized by
`FiniteField.geometricFrobenius_pow_card`: it is the unique `#k`-th root. -/
noncomputable def geometricFrobenius : K ≃ₐ[k] K :=
  letI : Fintype k := Fintype.ofFinite k
  (frobeniusAlgEquivOfAlgebraic k K).symm

@[simp]
theorem geometricFrobenius_pow_card (x : K) : geometricFrobenius k K x ^ Nat.card k = x := by
  let : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  exact (frobeniusAlgEquivOfAlgebraic k K).apply_symm_apply x

/-- The geometric Frobenius of an algebraic extension of a finite field `k` is
characterized as the inverse of raising to the `#k`-th power. -/
theorem geometricFrobenius_eq_iff {x y : K} :
    geometricFrobenius k K x = y ↔ y ^ Nat.card k = x := by
  refine ⟨fun h ↦ h ▸ geometricFrobenius_pow_card k K x, fun h ↦ h ▸ ?_⟩
  let : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  exact (frobeniusAlgEquivOfAlgebraic k K).symm_apply_apply y


end FiniteField
