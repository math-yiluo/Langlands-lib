/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Complements on finite fields

## Main results

- `FiniteField.pow_card_eq_self_iff_mem_range`: the image of an embedding `ι : E →+* L` of a
  finite field `E` into a field `L` consists exactly of the elements of `L` fixed by the
  `#E`-power map.
- `FiniteField.coe_frobeniusAlgHom_pow`: the powers of the Frobenius `x ↦ x ^ q` of an algebra
  over a finite field with `q` elements are the `q ^ n`-power maps.
-/

@[expose] public section

namespace FiniteField

/-- The image of an embedding `ι : E →+* L` of a finite field `E` into a field `L` consists
exactly of the roots of `X ^ #E - X`: every element of `E` is such a root, and this
polynomial has at most `#E` roots in `L`. -/
theorem pow_card_eq_self_iff_mem_range {E L : Type*} [Field E] [Fintype E] [Field L]
    (ι : E →+* L) {x : L} : x ^ Fintype.card E = x ↔ x ∈ Set.range ι := by
  classical
  refine ⟨fun hx ↦ ?_, fun ⟨a, ha⟩ ↦ by rw [← ha, ← map_pow, pow_card]⟩
  have hq : 1 < Fintype.card E := Fintype.one_lt_card
  set f : Polynomial L := Polynomial.X ^ Fintype.card E - Polynomial.X
  have hf : f ≠ 0 := X_pow_card_sub_X_ne_zero L hq
  have hroot {y : L} : y ∈ f.roots.toFinset ↔ y ^ Fintype.card E = y := by
    simp [f, Polynomial.mem_roots hf, sub_eq_zero]
  have himage : Finset.univ.image ι = f.roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
      rw [hroot, ← map_pow, pow_card]
    · rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ]
      calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
        _ ≤ f.natDegree := Polynomial.card_roots' f
        _ = Fintype.card E := X_pow_card_sub_X_natDegree_eq L hq
  have hx' : x ∈ f.roots.toFinset := hroot.mpr hx
  rw [← himage] at hx'
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx'
  exact ⟨a, rfl⟩

/-- The `n`-th power of the Frobenius endomorphism `x ↦ x ^ q` of an algebra over a finite field
with `q` elements is the `q ^ n`-power map. -/
theorem coe_frobeniusAlgHom_pow (K R : Type*) [Field K] [Fintype K] [CommRing R] [Algebra K R]
    (n : ℕ) : ⇑(frobeniusAlgHom K R ^ n) = (· ^ (Fintype.card K ^ n)) := by
  rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate]


end FiniteField
