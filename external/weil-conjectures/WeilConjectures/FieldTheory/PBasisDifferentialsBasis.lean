/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Kaehler.Basic

import WeilConjectures.FieldTheory.PIndependentEvaluationKernel

/-!
# Differentials of a p-basis

Source: Stacks Project, More on Algebra, Definition 07P1 and Lemma 07P2, implication
(a) implies (b) (blueprint: lem-weil-pbc-p-basis-differentials-basis).
-/

@[expose] public section

universe u v w

namespace KaehlerDifferential

/-- Source: Stacks Project, Tags 07P1 and 07P2, implication (a) implies (b).
(blueprint: lem-weil-pbc-p-basis-differentials-basis)

The differentials of a p-basis form a basis of the relative differentials.

Proof:
1. Every k-derivation kills B = kK^p: use the p-th power rule and induction on
   the field adjunction, including the inverse rule. The universal derivation
   therefore kills B. Leibniz shows that the differential of every monomial
   lies in the K-span of the dt_i. Expanding every element in the given
   monomial basis proves that these differentials span all of Ω[K/k].
2. The same basis expansion proves evaluation B[X_i] → K is surjective.
3. The bounded monomials are independent. Apply
   `MvPolynomial.aeval_pderiv_eq_zero_of_pIndependent` to show that each partial
   derivative preserves the evaluation kernel. Descend it along evaluation
   using `Derivation.liftOfSurjective`, and restrict scalars to k. This gives
   derivations δ_i with δ_i(t_j) = 1 for i = j and 0 otherwise.
4. The universal property of Ω[K/k] turns the δ_i into K-linear forms dual to
   the dt_i. Hence the dt_i are linearly independent. Combine independence
   and spanning with `Module.Basis.mk`. The argument uses finite supports
   throughout and includes both infinite and empty I. -/
theorem exists_basis_differentials_of_pBasis
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP K p]
    {I : Type w} (t : I → K)
    (hmon : ∃ b : Module.Basis {E : I →₀ ℕ // ∀ i : I, E i < p}
        (IntermediateField.adjoin k (Set.range (fun x : K => x ^ p))) K,
      ∀ E, b E = E.val.prod (fun i e => t i ^ e)) :
    ∃ b : Module.Basis I K (KaehlerDifferential k K),
      ∀ i : I, b i = D k K (t i) := by
  classical
  obtain ⟨b, hb⟩ := hmon
  let B := IntermediateField.adjoin k (Set.range (fun x : K => x ^ p))
  let d := D k K
  let S := Submodule.span K (Set.range (fun i => d (t i)))
  have hB : ∀ c : B, d (c : K) = 0 := by
    suffices h : ∀ x : K, x ∈ B → d x = 0 from fun c => h c c.property
    intro x hx
    change x ∈ IntermediateField.adjoin k _ at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [d.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero]
      simp
    | algebraMap x => exact d.map_algebraMap x
    | add x y hx hy hdx hdy => simp [hdx, hdy]
    | inv x hx hdx => rw [d.leibniz_inv, hdx, smul_zero]
    | mul x y hx hy hdx hdy => simp [hdx, hdy]
  have hprod : ∀ E : I →₀ ℕ, d (E.prod (fun i n => t i ^ n)) ∈ S := by
    intro E
    induction E using Finsupp.induction with
    | zero => simp [S]
    | @single_add i n E hi hn ih =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _)
        (fun _ _ _ => pow_add _ _ _)]
      simp only [Finsupp.prod_single_index, pow_zero]
      rw [d.leibniz, d.leibniz_pow]
      rw [← Nat.cast_smul_eq_nsmul K]
      apply S.add_mem (S.smul_mem _ ih)
      apply S.smul_mem
      apply S.smul_mem
      apply S.smul_mem
      exact Submodule.subset_span (Set.mem_range_self i)
  have hspan : S = ⊤ := by
    apply top_unique
    rw [← span_range_derivation k K]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [map_sum]
    apply S.sum_mem
    intro E hE
    change d ((b.repr a E : K) * b E) ∈ S
    rw [d.leibniz, hB, smul_zero, add_zero, hb]
    exact S.smul_mem _ (hprod E.val)
  let e : MvPolynomial I B →ₐ[B] K := MvPolynomial.aeval t
  have he : Function.Surjective e := by
    intro a
    refine ⟨(b.repr a).sum (fun E c => MvPolynomial.monomial E.val c), ?_⟩
    rw [map_finsuppSum]
    convert b.linearCombination_repr a using 1
    apply Finsupp.sum_congr
    intro E c
    simp [e, MvPolynomial.aeval_monomial, hb, Algebra.smul_def]
  have hker (i : I) : ∀ f, e f = 0 → e (MvPolynomial.pderiv i f) = 0 := by
    exact MvPolynomial.aeval_pderiv_eq_zero_of_pIndependent p t
      (by
        have heq : (fun E => E.val.prod (fun i e => t i ^ e)) = b := (funext hb).symm
        rw [heq]
        exact b.linearIndependent) i
  let δ (i : I) : Derivation k K K :=
    (Derivation.liftOfSurjective he (hker i)).restrictScalars k
  have hδ (i j : I) : δ i (t j) = if i = j then 1 else 0 := by
    change Derivation.liftOfSurjective he (hker i) (t j) = _
    rw [← MvPolynomial.aeval_X (R := B) t j]
    change Derivation.liftOfSurjective he (hker i) (e (MvPolynomial.X j)) = _
    rw [Derivation.liftOfSurjective_apply]
    by_cases hij : i = j
    · subst j
      simp [e]
    · simp [e, hij, Ne.symm hij]
  have hli : LinearIndependent K (fun i => d (t i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _
      (fun i => (δ i).liftKaehlerDifferential)
    · intro i j hij
      simp [d, hδ, hij]
    · intro i
      simp [d, hδ]
  exact ⟨Module.Basis.mk hli (by rw [show Submodule.span K _ = S from rfl, hspan]),
    fun i => Module.Basis.mk_apply _ _ i⟩

end KaehlerDifferential
