/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Towers of p-th roots in finite purely inseparable extensions

Source: literature/stacks-project/fields.tex, Lemma Tag 09HI (blueprint:
lem-weil-pbc-purely-inseparable-pth-root-tower).
-/

@[expose] public section

universe u v

open scoped Polynomial

namespace IsPurelyInseparable

private theorem first_root
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    [IsPurelyInseparable F E] [FiniteDimensional F E]
    (hne : (⊥ : IntermediateField F E) ≠ ⊤) :
    ∃ a : E, a ^ p ∈ (⊥ : IntermediateField F E) ∧
      a ∉ (⊥ : IntermediateField F E) ∧
      Module.finrank F (IntermediateField.adjoin F ({a} : Set E)) = p := by
  classical
  have : CharP E p := (Algebra.charP_iff F E p).mp inferInstance
  have hx : ∃ x : E, x ∉ (⊥ : IntermediateField F E) := by
    by_contra h
    apply hne
    apply top_unique
    intro x _
    exact not_not.mp (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hx
  have hex := IsPurelyInseparable.pow_mem F p x
  let r := Nat.find hex
  have hr : x ^ p ^ r ∈ (⊥ : IntermediateField F E) := Nat.find_spec hex
  have hrpos : 0 < r := by
    by_contra h
    have : r = 0 := by omega
    simp only [this, pow_zero, pow_one] at hr
    exact hx hr
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  let a := x ^ p ^ k
  have ha : a ∉ (⊥ : IntermediateField F E) := by
    exact Nat.find_min hex (by omega)
  have hap : a ^ p ∈ (⊥ : IntermediateField F E) := by
    simpa [a, hk, pow_succ, pow_mul] using hr
  obtain ⟨b, hb⟩ := hap
  change algebraMap F E b = a ^ p at hb
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C b) := by
    apply X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p)
    intro c hc
    have he : (algebraMap F E c) ^ p = a ^ p := by
      rw [← map_pow, hc, hb]
    have heq : algebraMap F E c = a := frobenius_inj E p he
    exact ha ⟨c, heq⟩
  have hmin : minpoly F a = Polynomial.X ^ p - Polynomial.C b := by
    symm
    apply minpoly.eq_of_irreducible_of_monic hirr
    · simp [hb]
    · exact Polynomial.monic_X_pow_sub_C b (Fact.out : Nat.Prime p).ne_zero
  refine ⟨a, ⟨b, hb⟩, ha, ?_⟩
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a), hmin,
    Polynomial.natDegree_X_pow_sub_C]

private theorem cons_range (E : Type v) (a : E) (γ : ℕ → E) (k : ℕ) :
    Set.range (fun j : Fin (k + 1) =>
      (match (j : ℕ) with | 0 => a | i + 1 => γ i)) =
      {a} ∪ Set.range (fun j : Fin k => γ j) := by
  ext y
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    cases j with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨⟨j, by omega⟩, rfl⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨⟨0, by omega⟩, rfl⟩
    · exact ⟨⟨(j : ℕ) + 1, by have := j.isLt; omega⟩, rfl⟩

private theorem tower_aux
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    [IsPurelyInseparable F E] [FiniteDimensional F E]
    (K : IntermediateField F E) :
    ∃ (n : ℕ) (α : ℕ → E),
      (∀ x : E, x ∈ IntermediateField.adjoin K
        (Set.range (fun j : Fin n => α j))) ∧
      (∀ i : ℕ, i < n →
        α i ^ p ∈ IntermediateField.adjoin K (Set.range (fun j : Fin i => α j)) ∧
        α i ∉ IntermediateField.adjoin K (Set.range (fun j : Fin i => α j))) := by
  classical
  have : CharP E p := (Algebra.charP_iff F E p).mp inferInstance
  generalize hd : Module.finrank K E = d
  induction d using Nat.strong_induction_on generalizing K with
  | h d ih =>
    have : CharP K p := (Algebra.charP_iff K E p).mpr inferInstance
    by_cases htriv : (⊥ : IntermediateField K E) = ⊤
    · refine ⟨0, fun _ => 0, ?_, ?_⟩
      · intro x
        simpa only [Fin.isEmpty, Set.range_eq_empty, IntermediateField.adjoin_empty,
          htriv] using (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K E))
      · intro i hi
        omega
    obtain ⟨a, hap, ha, hdegree⟩ := first_root K E p htriv
    let L := (IntermediateField.adjoin K ({a} : Set E)).restrictScalars F
    have hsmall : Module.finrank L E < d := by
      have hm := Module.finrank_mul_finrank K (IntermediateField.adjoin K {a}) E
      have hpos : 0 < Module.finrank (IntermediateField.adjoin K {a}) E :=
        Module.finrank_pos
      rw [hdegree, hd] at hm
      change Module.finrank (IntermediateField.adjoin K {a}) E < d
      have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
      nlinarith
    obtain ⟨n, γ, hgen, hsteps⟩ := ih _ hsmall L rfl
    let α : ℕ → E := fun i => match i with | 0 => a | j + 1 => γ j
    have hprefix (i : ℕ) :
        IntermediateField.adjoin K (Set.range (fun j : Fin (i + 1) => α j)) =
          (IntermediateField.adjoin (IntermediateField.adjoin K ({a} : Set E))
            (Set.range (fun j : Fin i => γ j))).restrictScalars K := by
      rw [show Set.range (fun j : Fin (i + 1) => α j) =
          {a} ∪ Set.range (fun j : Fin i => γ j) from cons_range E a γ i]
      exact (IntermediateField.adjoin_adjoin_left K {a} _).symm
    refine ⟨n + 1, α, ?_, ?_⟩
    · intro x
      rw [hprefix]
      exact hgen x
    · intro i hi
      cases i with
      | zero =>
        simpa only [Fin.isEmpty, Set.range_eq_empty, IntermediateField.adjoin_empty]
          using And.intro hap ha
      | succ i =>
        rw [hprefix]
        exact hsteps i (by omega)

/-- Source: Stacks Tag 09HI. Strong induction on the degree: choose an element outside
F, take the last p-power before it enters F, and adjoin this p-th root. The root has
irreducible polynomial X^p-t and hence degree p. The remaining degree decreases by
multiplicativity. Apply induction and prepend the root; the empty tower handles degree one.
(blueprint: lem-weil-pbc-purely-inseparable-pth-root-tower)
-/
private theorem exists_pth_root_generators
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    [IsPurelyInseparable F E] [FiniteDimensional F E] :
    ∃ (n : ℕ) (α : ℕ → E),
      (∀ x : E, x ∈ IntermediateField.adjoin F (Set.range (fun j : Fin n => α j))) ∧
      (∀ i : ℕ, i < n →
        (α i) ^ p ∈ IntermediateField.adjoin F (Set.range (fun j : Fin i => α j))) ∧
      (∀ i : ℕ, i < n →
        ¬ ∃ x : E,
          x ∈ IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)) ∧
            x ^ p = (α i) ^ p) ∧
      (∀ i : ℕ, i < n →
        Module.finrank (IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)))
          (IntermediateField.adjoin
            (IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)))
            ({α i} : Set E)) = p) := by
  classical
  have : CharP E p := (Algebra.charP_iff F E p).mp inferInstance
  obtain ⟨n, α, hgen, hsteps⟩ := tower_aux F E p ⊥
  have hprefix (i : ℕ) :
      (IntermediateField.adjoin (⊥ : IntermediateField F E)
        (Set.range (fun j : Fin i => α j))).restrictScalars F =
        IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)) := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, bot_sup_eq]
  have hpows (i : ℕ) (hi : i < n) :
      α i ^ p ∈ IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)) := by
    rw [← hprefix]
    exact (hsteps i hi).1
  have hnots (i : ℕ) (hi : i < n) :
      ¬ ∃ x : E,
        x ∈ IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)) ∧
        x ^ p = α i ^ p := by
    rintro ⟨x, hx, heq⟩
    have he : x = α i := frobenius_inj E p heq
    subst x
    rw [← hprefix] at hx
    exact (hsteps i hi).2 hx
  refine ⟨n, α, ?_, hpows, hnots, ?_⟩
  · intro x
    rw [← hprefix]
    exact hgen x
  · intro i hi
    let M := IntermediateField.adjoin F (Set.range (fun j : Fin i => α j))
    let b : M := ⟨α i ^ p, hpows i hi⟩
    have hmin : minpoly M (α i) = Polynomial.X ^ p - Polynomial.C b := by
      symm
      apply minpoly.eq_of_irreducible_of_monic
      · apply X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p)
        intro c hc
        apply hnots i hi
        refine ⟨c, c.property, ?_⟩
        exact congrArg (algebraMap M E) hc
      · simp [b]
      · exact Polynomial.monic_X_pow_sub_C b (Fact.out : Nat.Prime p).ne_zero
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := M) (α i)),
      hmin, Polynomial.natDegree_X_pow_sub_C]

/-- A finite purely inseparable extension is generated by successive p-th roots.
Source: Fields, Lemma Tag 09HI and its proof.
The final-step consequence follows by polynomial evaluation.
Proof: induct on the finite degree. For degree one use the empty tower. Otherwise choose an
outside element and take its least p-power lying in the base; the preceding power is a p-th
root outside the base. Frobenius injectivity shows its p-th power is not a p-th power in the
base. Irreducibility of X^p - t (the node x-pow-p-minus-t-irreducible) and the
simple-algebraic-extension-power-basis lemma give degree p. Degree multiplicativity makes
the remaining extension smaller; apply induction and concatenate the generators. For a
nontrivial extension, take the final preceding field and final generator. Subfields inherit
finiteness and pure inseparability, and multiplicativity gives the strict degree inequality.
Evaluation at the last generator is surjective by its power basis; division by the monic
X^p - t identifies its kernel, giving the displayed quotient-algebra isomorphism.
(blueprint: lem-weil-pbc-purely-inseparable-pth-root-tower)
-/
theorem exists_pth_root_tower
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    [IsPurelyInseparable F E] [FiniteDimensional F E] :
    ∃ (n : ℕ) (α : ℕ → E),
      (∀ x : E, x ∈ IntermediateField.adjoin F (Set.range (fun j : Fin n => α j))) ∧
      (∀ i : ℕ, i < n →
        (α i) ^ p ∈ IntermediateField.adjoin F (Set.range (fun j : Fin i => α j))) ∧
      (∀ i : ℕ, i < n →
        ¬ ∃ x : E,
          x ∈ IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)) ∧
            x ^ p = (α i) ^ p) ∧
      (∀ i : ℕ, i < n →
        Module.finrank (IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)))
          (IntermediateField.adjoin
            (IntermediateField.adjoin F (Set.range (fun j : Fin i => α j)))
            ({α i} : Set E)) = p) ∧
      ((⊥ : IntermediateField F E) ≠ ⊤ →
        ∃ (M : IntermediateField F E) (β : E),
          0 < n ∧ M = IntermediateField.adjoin F
            (Set.range (fun j : Fin (n - 1) => α j)) ∧ β = α (n - 1) ∧
          M < ⊤ ∧ Module.Finite F M ∧ IsPurelyInseparable F M ∧
          Module.finrank F M < Module.finrank F E ∧
          (∀ x : E, x ∈ IntermediateField.adjoin M ({β} : Set E)) ∧
          Module.finrank M E = p ∧
          (∃ b : M, algebraMap M E b = β ^ p) ∧
          (¬ ∃ x : E, x ∈ M ∧ x ^ p = β ^ p) ∧
          (∃ b : M, algebraMap M E b = β ^ p ∧
            Nonempty (E ≃ₐ[M] M[X] ⧸ Ideal.span {Polynomial.X ^ p - Polynomial.C b}))) := by
  classical
  obtain ⟨n, α, hgen, hpow, hnot, hdeg⟩ := exists_pth_root_generators F E p
  refine ⟨n, α, hgen, hpow, hnot, hdeg, ?_⟩
  intro hne
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    subst n
    apply hne
    apply top_unique
    intro x hx
    simpa using hgen x
  let k := n - 1
  have hkn : k < n := by dsimp [k]; omega
  have hnk : n = k + 1 := by dsimp [k]; omega
  let M := IntermediateField.adjoin F (Set.range (fun j : Fin k => α j))
  let β := α k
  have hbpow : β ^ p ∈ M := hpow k hkn
  have hbnot : ¬ ∃ x : E, x ∈ M ∧ x ^ p = β ^ p := hnot k hkn
  have hlast : ∀ x : E, x ∈ IntermediateField.adjoin M ({β} : Set E) := by
    intro x
    have hrange : Set.range (fun j : Fin n => α j) =
        Set.range (fun j : Fin k => α j) ∪ {β} := by
      ext y
      simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩
        by_cases hj : (j : ℕ) < k
        · exact Or.inl ⟨⟨j, hj⟩, rfl⟩
        · have hjk : (j : ℕ) = k := by have := j.isLt; omega
          exact Or.inr (congrArg α hjk)
      · rintro (⟨j, rfl⟩ | rfl)
        · exact ⟨⟨j, lt_trans j.isLt hkn⟩, rfl⟩
        · exact ⟨⟨k, hkn⟩, rfl⟩
    have heq := IntermediateField.adjoin_adjoin_left F
      (Set.range (fun j : Fin k => α j)) ({β} : Set E)
    have hx := hgen x
    rw [hrange, ← heq] at hx
    exact hx
  have htop : IntermediateField.adjoin M ({β} : Set E) = ⊤ := by
    apply top_unique
    intro x hx
    exact hlast x
  have hME : Module.finrank M E = p := by
    have hd := hdeg k hkn
    rw [htop, IntermediateField.finrank_top'] at hd
    exact hd
  have hMlt : M < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    have hpone : p = 1 := by
      rw [heq, IntermediateField.finrank_top] at hME
      exact hME.symm
    exact (Fact.out : Nat.Prime p).ne_one hpone
  have hsmall : Module.finrank F M < Module.finrank F E := by
    have hm := Module.finrank_mul_finrank F M E
    have hpos : 0 < Module.finrank F M := Module.finrank_pos
    have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
    rw [hME] at hm
    nlinarith
  let b : M := ⟨β ^ p, hbpow⟩
  have hmin : minpoly M β = Polynomial.X ^ p - Polynomial.C b := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · apply X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p)
      intro c hc
      apply hbnot
      refine ⟨c, c.property, ?_⟩
      exact congrArg (algebraMap M E) hc
    · simp [b]
    · exact Polynomial.monic_X_pow_sub_C b (Fact.out : Nat.Prime p).ne_zero
  have halg : Algebra.adjoin M ({β} : Set E) = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic β)).mp htop
  have hequiv : Nonempty (E ≃ₐ[M]
      M[X] ⧸ Ideal.span {Polynomial.X ^ p - Polynomial.C b}) := by
    have e := (minpoly.equivAdjoin (Algebra.IsIntegral.isIntegral (R := M) β)).trans
      ((Subalgebra.equivOfEq _ _ halg).trans Subalgebra.topEquiv)
    rw [hmin] at e
    exact ⟨e.symm⟩
  exact ⟨M, β, hn, rfl, rfl, hMlt, inferInstance, inferInstance, hsmall,
    hlast, hME, ⟨b, rfl⟩, hbnot, ⟨b, rfl, hequiv⟩⟩

end IsPurelyInseparable
