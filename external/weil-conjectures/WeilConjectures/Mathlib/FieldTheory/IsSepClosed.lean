/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.SeparableClosure

/-!
# A separable closure is the union of its finite separable subextensions

A separable closure of a field `k` is Mathlib's `IsSepClosure k ks`. Here we record that `ks` is
the directed union of its finite separable subextensions, so that `ks` is their filtered colimit.

## Main statements

- `IsSepClosure.exists_intermediateField_mem`: every element of a separable closure lies in a
  finite separable subextension (blueprint `def-pd-separable-closure`).
- `IsSepClosed.instInfinite`: a separably closed field is infinite.
- `RingHom.exists_comp_eq_of_isSepClosed`: an embedding of a separable extension into a field
  extension of a separably closed field `L` lands in `L`.
- `IsSepClosed.iff_exists_root`, `IsSepClosed.iff_forall_finrank_eq_one`: a field is separably
  closed iff every nonconstant separable polynomial has a root iff it has no nontrivial finite
  separable extension (blueprint `def-pc-separably-closed`).
- `IsSepClosed.finrank_eq_one_of_isSeparable`: separable extensions of a separably closed field
  are trivial (blueprint `lem-pc-sepclosed-finite-sep-trivial`).
-/

@[expose] public section

universe u v

open IntermediateField

/-- **A separable closure is the union of its finite separable subextensions.** Let `ks` be a
separable closure of `k`. Every `x ∈ ks` lies in a subextension `K` of `ks/k` that is finite and
separable over `k`, namely `k⟮x⟯`; hence `ks = colim K` over the finite separable subextensions.

The separable closure itself is Mathlib's `IsSepClosure`.

(blueprint: `def-pd-separable-closure`) -/
theorem IsSepClosure.exists_intermediateField_mem (k : Type u) {ks : Type v} [Field k] [Field ks]
    [Algebra k ks] [IsSepClosure k ks] (x : ks) :
    ∃ K : IntermediateField k ks, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧ x ∈ K := by
  have := IsSepClosure.separable (k := k) (K := ks)
  have hx : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  exact ⟨k⟮x⟯, adjoin.finiteDimensional hx.isIntegral,
    (isSeparable_adjoin_simple_iff_isSeparable k ks).mpr hx, mem_adjoin_simple_self k x⟩


/-- A separably closed field is infinite: over a finite field `k` with `q` elements the
polynomial `X ^ q - X - 1` is separable (its derivative is `-1`) but has no root, since
`a ^ q = a` for every `a ∈ k`. -/
instance (priority := 100) IsSepClosed.instInfinite (k : Type u) [Field k] [IsSepClosed k] :
    Infinite k := by
  refine Infinite.of_not_fintype fun _ ↦ ?_
  obtain ⟨a, ha⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (1 : k) (-1) (-1)
    (FiniteField.cast_card_eq_zero k) (Fintype.one_lt_card (α := k)) (by simp)
  simp [FiniteField.pow_card] at ha

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.FieldTheory.IsSepClosed`) -/

/-- `IsSepClosed` transfers along a ring isomorphism of fields. -/
theorem IsSepClosed.of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') [IsSepClosed k] : IsSepClosed k' := by
  refine ⟨fun p hp => ?_⟩
  have hsplit : (p.map e.symm.toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ hp.map
  have hpush := hsplit.map e.toRingHom
  rwa [Polynomial.map_map, e.toRingHom_comp_symm_toRingHom, Polynomial.map_id] at hpush

/-- If `E` is separable over `F`, `L` is separably closed and `c : E ⟶ Ω` agrees on `F` with
`b ≫ β` for `b : F ⟶ L` and `β : L ⟶ Ω`, then `c` factors through `β`. -/
lemma RingHom.exists_comp_eq_of_isSepClosed {F E L Ω : Type*} [Field F] [Field E] [Field L]
    [Field Ω] [Algebra F E] [Algebra.IsSeparable F E] [IsSepClosed L] (b : F →+* L)
    (β : L →+* Ω) (c : E →+* Ω) (h : c.comp (algebraMap F E) = β.comp b) :
    ∃ c' : E →+* L, β.comp c' = c := by
  have hsub : ∀ e, c e ∈ β.range := by
    intro e
    have hsep : (minpoly F e).Separable := Algebra.IsSeparable.isSeparable F e
    have hspl : ((minpoly F e).map b).Splits := IsSepClosed.splits_codomain _ hsep
    have hne : (minpoly F e).map b ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsSeparable.isIntegral F e))
    refine hspl.mem_range_of_isRoot hne ?_
    rw [Polynomial.map_map, ← h, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  let e := RingEquiv.ofBijective β.rangeRestrict ⟨fun a b hab ↦ β.injective
    (congr_arg Subtype.val hab), β.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (c.codRestrict β.range hsub), RingHom.ext fun x ↦ ?_⟩
  change ((e (e.symm ⟨c x, hsub x⟩)) : Ω) = c x
  rw [e.apply_symm_apply]


/-! ### Characterisations of separably closed fields -/

namespace IsSepClosed

open Polynomial

variable (k : Type u) [Field k]

/-- **Separably closed fields.** A field `k` is separably closed (Mathlib's `IsSepClosed k`, every
separable polynomial splits) if and only if every nonconstant separable polynomial over `k` has a
root in `k`.

(blueprint: `def-pc-separably-closed`) -/
theorem iff_exists_root :
    IsSepClosed k ↔ ∀ p : k[X], p.degree ≠ 0 → p.Separable → ∃ x, p.IsRoot x :=
  ⟨fun _ p hp hsep ↦ exists_root p hp hsep, fun h ↦ of_exists_root k fun _ _ hirr hsep ↦
    h _ (degree_pos_of_irreducible hirr).ne' hsep⟩

/-- **A separably closed field has no nontrivial separable extension.** If `k` is separably
closed, every separable field extension `K / k`, in particular every finite one, is trivial:
`[K : k] = 1`.

(blueprint: `lem-pc-sepclosed-finite-sep-trivial`) -/
theorem finrank_eq_one_of_isSeparable [IsSepClosed k] (K : Type v) [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] : Module.finrank k K = 1 :=
  ((AlgEquiv.ofBijective (Algebra.ofId k K) (algebraMap_bijective k K)).toLinearEquiv.finrank_eq
    ).symm.trans (Module.finrank_self k)

/-- **The two formulations of separable closedness agree.** A field `k` is separably closed if and
only if it has no nontrivial finite separable field extension. One direction is
`IsSepClosed.finrank_eq_one_of_isSeparable`; conversely, for a separable irreducible polynomial `p`
with a root `α` in an algebraic closure, `k⟮α⟯` is a finite separable extension of degree
`deg p`, so `deg p = 1` and `p` has a root in `k`.

(blueprint: `rem-ptr-pc-separably-closed-1`, `def-pc-separably-closed`) -/
theorem iff_forall_finrank_eq_one :
    IsSepClosed k ↔ ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
      [Algebra.IsSeparable k K], Module.finrank k K = 1 := by
  refine ⟨fun _ K _ _ _ _ ↦ finrank_eq_one_of_isSeparable k K, fun h ↦ ?_⟩
  refine of_exists_root k fun p _ hirr hsep ↦ ?_
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure k) p
    (degree_pos_of_irreducible hirr).ne'
  have hp0 : p ≠ 0 := hirr.ne_zero
  have hint : IsIntegral k α := ⟨p * C p.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hp0, by
    simp [eval₂_mul, ← aeval_def, hα]⟩
  have hαsep : IsSeparable k α := hsep.of_dvd (minpoly.dvd k α hα)
  have : FiniteDimensional k k⟮α⟯ := adjoin.finiteDimensional hint
  have : Algebra.IsSeparable k k⟮α⟯ := (isSeparable_adjoin_simple_iff_isSeparable k _).mpr hαsep
  have h1 := h k⟮α⟯
  rw [adjoin.finrank hint, minpoly.natDegree_eq_one_iff] at h1
  obtain ⟨a, ha⟩ := h1
  refine ⟨a, (algebraMap k (AlgebraicClosure k)).injective ?_⟩
  rw [map_zero, ← hα, ← ha, ← eval₂_at_apply, aeval_def]


end IsSepClosed

/-- A separably closed field is separably closed for the field structure
`(Field.toIsField K).toField` recovered from its ring structure. -/
theorem IsField.isSepClosed_toField {K : Type*} [hK : Field K] [hs : IsSepClosed K] :
    letI := (Field.toIsField K).toField; IsSepClosed K :=
  @IsSepClosed.mk K (Field.toIsField K).toField fun p hp ↦
    @IsSepClosed.splits_of_separable K hK hs p hp
