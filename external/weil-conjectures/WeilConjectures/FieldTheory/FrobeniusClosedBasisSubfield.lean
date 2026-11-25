/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.FrobeniusClosedBasis
public import WeilConjectures.FieldTheory.AdjoinSimplePow

/-!
# Frobenius-closed bases of function fields inside a bigger field

Let `ℓ` be a field of characteristic `p`, `k ≤ E` subfields of `ℓ` with `k` algebraically closed,
and `x ∈ E` transcendental over `k` such that `E` is a finite separable extension of `k⟮x⟯`.
Then `E` has a Frobenius-closed `k`-basis `1, w i ^ p ^ n`
(`FrobeniusClosedBasis.exists_frobeniusClosed_basis`), and `x` is a polynomial of degree `< p`
with coefficients in `E ^ p` in any element `ρ ∈ E` which is not a `p`-th power in `E`: indeed
`E = E ^ p (x)` has degree `p` over `E ^ p`, so `E = E ^ p (ρ)`.
-/

@[expose] public section

universe u

open Polynomial IntermediateField

namespace FrobeniusClosedBasis

/-- **Frobenius-closed bases of a function field inside a bigger field**: the basis part of
`FrobeniusClosedBasis.exists_of_subfield`. -/
theorem exists_basis_of_subfield {ℓ : Type u} [Field ℓ] (p : ℕ) [Fact p.Prime] [CharP ℓ p]
    (k E : Subfield ℓ) (hkE : k ≤ E) [IsAlgClosed k] {x : ℓ} (hxE : x ∈ E)
    (hx : Transcendental k x)
    (hfin : ∃ N : ℕ, ∀ (n : ℕ) (e : Fin n → ℓ), (∀ i, e i ∈ E) →
      LinearIndependent (IntermediateField.adjoin k {x}) e → n ≤ N)
    (hsep : ∀ e ∈ E, IsSeparable (IntermediateField.adjoin k {x}) e) :
    ∃ (ι : Type u) (w : ι → ℓ), (∀ i, w i ∈ E) ∧
      LinearIndependent k (fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2) ∧
      ∀ e ∈ E, e ∈ Submodule.span k
        (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2) := by
  -- `E` as an extension of `k`, and as an extension of `k⟮x⟯`
  let E' : IntermediateField k ℓ := E.toIntermediateField fun c ↦ hkE c.2
  let L : IntermediateField k⟮x⟯ ℓ := extendScalars (adjoin_simple_le_iff.2 hxE : k⟮x⟯ ≤ E')
  have : Module.Finite k⟮x⟯ L := by
    obtain ⟨N, hN⟩ := hfin
    refine Module.rank_lt_aleph0_iff.1
      ((rank_le (n := N) fun s hs ↦ ?_).trans_lt (Cardinal.natCast_lt_aleph0))
    exact hN _ (fun j ↦ ((s.equivFin.symm j : L) : ℓ)) (fun j ↦ (s.equivFin.symm j : L).2)
      ((hs.comp _ s.equivFin.symm.injective).map' L.val.toLinearMap
        (LinearMap.ker_eq_bot_of_injective L.val.injective))
  have : Algebra.IsSeparable k⟮x⟯ L := ⟨fun y ↦ IsSeparable.of_algHom k⟮x⟯ L.val (hsep _ y.2)⟩
  -- transport to `k⟮x'⟯ ≤ E'`
  let x' : E' := ⟨x, hxE⟩
  have hmap : (k⟮x'⟯).map E'.val = k⟮x⟯ := by
    rw [adjoin_map, Set.image_singleton]
    rfl
  let e₁ : k⟮x⟯ ≃+* k⟮x'⟯ :=
    (((k⟮x'⟯).equivMap E'.val).trans (equivOfEq hmap)).symm.toRingEquiv
  let e₂ : L ≃+* E' :=
    { toFun := fun y ↦ ⟨y.1, y.2⟩
      invFun := fun y ↦ ⟨y.1, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : (algebraMap k⟮x'⟯ E').comp (e₁ : k⟮x⟯ →+* k⟮x'⟯) =
      (e₂ : L →+* E').comp (algebraMap k⟮x⟯ L) := by
    ext c
    have h := congrArg Subtype.val
      ((k⟮x'⟯.equivMap E'.val).apply_symm_apply ((equivOfEq hmap).symm c))
    exact h
  have : FiniteDimensional k⟮x'⟯ E' := Module.Finite.of_equiv_equiv e₁ e₂ he
  have : Algebra.IsSeparable k⟮x'⟯ E' := Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he
  have : CharP E' p := (algebraMap E' ℓ).charP (algebraMap E' ℓ).injective p
  obtain ⟨ι, w, hli, hspan⟩ := exists_frobeniusClosed_basis k p x' fun h ↦ hx (h.algHom E'.val)
  -- push the basis to `ℓ`
  have hfam : (fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ (w i.1 : ℓ) ^ p ^ i.2) =
      E'.val.toLinearMap ∘ fun j ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2 := by
    funext j
    cases j <;> simp
  refine ⟨ι, fun i ↦ w i, fun i ↦ (w i).2, ?_, fun e he ↦ ?_⟩
  · rw [hfam]
    exact hli.map' E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)
  · rw [hfam, Set.range_comp, ← Submodule.map_span]
    have h' : (⟨e, he⟩ : E') ∈ Submodule.span k
        (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2) := by
      rw [hspan]
      exact Submodule.mem_top
    exact Submodule.mem_map_of_mem h'

/-- **`x` is a polynomial of degree `< p` in a non-`p`-th power**, with coefficients in `E ^ p`:
the last part of `FrobeniusClosedBasis.exists_of_subfield`. -/
theorem exists_eq_sum_pow_mul_pow_of_subfield {ℓ : Type u} [Field ℓ] (p : ℕ) [Fact p.Prime]
    [CharP ℓ p] (k E : Subfield ℓ) (hkE : k ≤ E) [IsAlgClosed k] {x : ℓ} (hxE : x ∈ E)
    (hx : Transcendental k x)
    (hsep : ∀ e ∈ E, IsSeparable (IntermediateField.adjoin k {x}) e) {ρ : ℓ} (hρE : ρ ∈ E)
    (hρ : ∀ z ∈ E, z ^ p ≠ ρ) :
    ∃ y : ℕ → ℓ, (∀ j, y j ∈ E) ∧ x = ∑ j ∈ Finset.range p, y j ^ p * ρ ^ j := by
  have hp := (Fact.out : p.Prime)
  -- the subfield `P = E ^ p`
  let P : Subfield ℓ := E.map (frobenius ℓ p)
  have : CharP P p := (algebraMap P ℓ).charP (algebraMap P ℓ).injective p
  have hmemP {c : ℓ} : c ∈ P ↔ ∃ z ∈ E, z ^ p = c := by
    simp [P, Subfield.mem_map, frobenius_def]
  have hEP {e : ℓ} (he : e ∈ E) : e ^ p ∈ P := hmemP.2 ⟨e, he, rfl⟩
  -- `x` is not a `p`-th power in `E`
  have hxP : x ∉ P := by
    intro hx'
    obtain ⟨y, hy, hyx⟩ := hmemP.1 hx'
    have : CharP k⟮x⟯ p := (algebraMap k⟮x⟯ ℓ).charP (algebraMap k⟮x⟯ ℓ).injective p
    obtain ⟨c, hc⟩ := mem_bot.1 ((hsep y hy).mem_bot_of_pow_mem (q := p)
      (mem_bot.2 ⟨⟨x, mem_adjoin_simple_self k x⟩, hyx.symm⟩))
    exact pow_ne_of_mem_adjoin_simple hp.one_lt hx (hc ▸ c.2) hyx
  -- `k⟮x⟯ ≤ P⟮x⟯`, as `k` is perfect
  have hkP {c : ℓ} (hc : c ∈ k) : c ∈ P := by
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (⟨c, hc⟩ : k) hp.pos
    exact hmemP.2 ⟨d, hkE d.2, congrArg Subtype.val hd⟩
  have hle {c : ℓ} (hc : c ∈ k⟮x⟯) : c ∈ P⟮x⟯ := by
    rw [← mem_toSubfield, adjoin_toSubfield] at hc
    refine Subfield.closure_le.2 ?_ hc
    rintro _ (⟨c, rfl⟩ | hy)
    · exact (P⟮x⟯).algebraMap_mem ⟨c, hkP c.2⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact mem_adjoin_simple_self P x
  -- `E = P⟮x⟯`: `E` is separable and purely inseparable over `P⟮x⟯`
  have hEPx {e : ℓ} (he : e ∈ E) : e ∈ P⟮x⟯ := by
    let φ : k⟮x⟯ →+* P⟮x⟯ := (algebraMap k⟮x⟯ ℓ).codRestrict (P⟮x⟯) fun c ↦ hle c.2
    have hφ : (algebraMap P⟮x⟯ ℓ).comp φ = algebraMap k⟮x⟯ ℓ := RingHom.ext fun _ ↦ rfl
    have hsep' : IsSeparable P⟮x⟯ e := by
      refine (Polynomial.Separable.map (hsep e he) (f := φ)).of_dvd (minpoly.dvd _ _ ?_)
      rw [aeval_def, eval₂_map, hφ, ← aeval_def, minpoly.aeval]
    have : CharP P⟮x⟯ p := (algebraMap P⟮x⟯ ℓ).charP (algebraMap P⟮x⟯ ℓ).injective p
    obtain ⟨c, hc⟩ := mem_bot.1 (hsep'.mem_bot_of_pow_mem (q := p)
      (mem_bot.2 ⟨⟨e ^ p, (P⟮x⟯).algebraMap_mem ⟨e ^ p, hEP he⟩⟩, rfl⟩))
    exact hc ▸ c.2
  -- elements of `E` outside `P` have degree `p` over `P`
  have hdeg {z : ℓ} (hz : z ∈ E) (hzP : z ∉ P) :
      IsIntegral P z ∧ Module.finrank P P⟮z⟯ = p := by
    have ha : algebraMap P ℓ ⟨z ^ p, hEP hz⟩ = z ^ p := rfl
    have hz' : z ∉ (⊥ : IntermediateField P ℓ) := fun h ↦ by
      obtain ⟨c, hc⟩ := mem_bot.1 h
      exact hzP (hc ▸ c.2)
    have hint : IsIntegral P z := .of_pow hp.pos (ha ▸ isIntegral_algebraMap)
    refine ⟨hint, ?_⟩
    rw [adjoin.finrank hint, minpoly_eq_X_pow_sub_C_of_notMem_bot hp ha hz',
      natDegree_X_pow_sub_C]
  obtain ⟨hxint, hxdeg⟩ := hdeg hxE hxP
  obtain ⟨hρint, hρdeg⟩ := hdeg hρE fun h ↦ by
    obtain ⟨z, hz, hzρ⟩ := hmemP.1 h
    exact hρ z hz hzρ
  -- hence `P⟮ρ⟯ = P⟮x⟯ ∋ x`
  have := adjoin.finiteDimensional hxint
  have heq : P⟮ρ⟯ = P⟮x⟯ :=
    eq_of_le_of_finrank_eq (adjoin_simple_le_iff.2 (hEPx hρE)) (hρdeg.trans hxdeg.symm)
  obtain ⟨f, hfdeg, hf⟩ := (adjoin.powerBasis hρint).exists_eq_aeval
    ⟨x, heq ▸ mem_adjoin_simple_self P x⟩
  have hfp : f.natDegree < p := by
    rw [← hρdeg, adjoin.finrank hρint]
    exact hfdeg
  have hx' : x = aeval ρ f :=
    (congrArg Subtype.val hf).trans (AdjoinSimple.coe_aeval_gen_apply P ρ f)
  choose y hy hyc using fun j ↦ hmemP.1 (f.coeff j).2
  refine ⟨y, hy, ?_⟩
  rw [hx', aeval_eq_sum_range' hfp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hyc, Algebra.smul_def]
  rfl

/-- **Frobenius-closed bases of a function field inside a bigger field.** -/
theorem exists_of_subfield {ℓ : Type u} [Field ℓ] (p : ℕ) [Fact p.Prime] [CharP ℓ p]
    (k E : Subfield ℓ) (hkE : k ≤ E) [IsAlgClosed k] {x : ℓ} (hxE : x ∈ E)
    (hx : Transcendental k x)
    (hfin : ∃ N : ℕ, ∀ (n : ℕ) (e : Fin n → ℓ), (∀ i, e i ∈ E) →
      LinearIndependent (IntermediateField.adjoin k {x}) e → n ≤ N)
    (hsep : ∀ e ∈ E, IsSeparable (IntermediateField.adjoin k {x}) e) :
    ∃ (ι : Type u) (w : ι → ℓ), (∀ i, w i ∈ E) ∧
      LinearIndependent k (fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2) ∧
      (∀ e ∈ E, e ∈ Submodule.span k
        (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2)) ∧
      ∀ ρ ∈ E, (∀ z ∈ E, z ^ p ≠ ρ) →
        ∃ y : ℕ → ℓ, (∀ j, y j ∈ E) ∧ x = ∑ j ∈ Finset.range p, y j ^ p * ρ ^ j := by
  obtain ⟨ι, w, hw, hli, hspan⟩ := exists_basis_of_subfield p k E hkE hxE hx hfin hsep
  exact ⟨ι, w, hw, hli, hspan, fun ρ hρE hρ ↦
    exists_eq_sum_pow_mul_pow_of_subfield p k E hkE hxE hx hsep hρE hρ⟩

end FrobeniusClosedBasis
