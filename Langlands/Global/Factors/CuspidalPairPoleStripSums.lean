import Langlands.Global.Factors.CuspidalPairPoleContinuation
import Langlands.Representation.RankinSelberg.NormalizedZetaCombination

/-! # Vertical-strip bounds from finite normalized sums with bounded weights -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.CuspidalPairPoles

open Langlands.RankinSelberg
open Polynomial Set

/-- The normalized values admit a finite combination equal to one, with each coefficient
bounded in vertical strips away from the two possible poles. -/
def HasBoundedNormalizedSum {ι : Type*} (R : ι → ℂ → ℂ) : Prop :=
  ∃ (A : Finset ι) (c : ι → ℂ → ℂ),
    (∀ i ∈ A, IsBoundedInVerticalStrips (c i)) ∧
    ∀ s ∉ ({0, 1} : Set ℂ), ∑ i ∈ A, c i s * R i s = 1

private theorem isBoundedInVerticalStrips_prod {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, IsBoundedInVerticalStrips (f i)) :
    IsBoundedInVerticalStrips (fun s => ∏ i, f i s) := by
  intro a b ε hε
  choose C hC using fun i => hf i a b ε hε
  refine ⟨∏ i, max (C i) 0, fun s ha hb h₀ h₁ => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
    (hC i s ha hb h₀ h₁).trans (le_max_left _ _)

/-- Products of local normalized values have a bounded finite sum indexed by the tuples
of their local tests. -/
theorem HasBoundedNormalizedSum.prod {Place : Type*} [Fintype Place] {Test : Place → Type*}
    {R : ∀ p, Test p → ℂ → ℂ} (h : ∀ p, HasBoundedNormalizedSum (R p)) :
    HasBoundedNormalizedSum (fun (i : ∀ p, Test p) s => ∏ p, R p (i p) s) := by
  classical
  choose A c hc hsum using h
  refine ⟨Fintype.piFinset A, fun i s => ∏ p, c p (i p) s, ?_, fun s hs => ?_⟩
  · intro i hi
    exact isBoundedInVerticalStrips_prod _ fun p => hc p (i p) ((Fintype.mem_piFinset.mp hi) p)
  · calc
      _ = ∏ p, ∑ j ∈ A p, c p j s * R p j s := by
        rw [Finset.prod_univ_sum]
        exact Finset.sum_congr rfl fun i _ => (Finset.prod_mul_distrib ..).symm
      _ = 1 := by simp only [hsum _ s hs, Finset.prod_const_one]

/-- The p-adic normalized rational zeta values admit such a sum, weighted by Laurent
polynomials evaluated at the spectral unit. -/
theorem hasBoundedNormalizedSum_of_normalizedGenerator
    {values : Set RationalFunctions} {P : ℂ[X]} (h : IsNormalizedGenerator values P)
    {q : ℕ} (hq : 1 < q) :
    HasBoundedNormalizedSum (fun (R : values) s =>
      laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s)
        (h.normalizedLaurent ⟨R, mem_zetaSpan R.property⟩)) := by
  refine ⟨h.reciprocalCombination.support,
    fun R s => laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) (h.reciprocalCombination R),
    ?_, fun s _ => h.reciprocalCombination_eval (spectralUnit (Nat.zero_lt_one.trans hq) s)⟩
  intro i _ a b ε _
  obtain ⟨C, hC⟩ := exists_bound_laurentEval_spectralUnit hq (h.reciprocalCombination i) a b
  exact ⟨C, fun s ha hb _ _ => hC s ha hb⟩

/-- The finite weighted sum of normalized identities transfers the bounds of the test
integrals to the completed function. -/
theorem isBoundedInVerticalStrips_of_bounded_normalized_sum {ι : Type*} (I R : ι → ℂ → ℂ)
    (Λ : ℂ → ℂ) (hR : HasBoundedNormalizedSum R)
    (hRelation : ∀ i s, s ∉ ({0, 1} : Set ℂ) → I i s = R i s * Λ s)
    (hBound : ∀ i, IsBoundedInVerticalStrips (I i)) : IsBoundedInVerticalStrips Λ := by
  obtain ⟨A, c, hc, hsum⟩ := hR
  refine isBoundedInVerticalStrips_of_normalized_sum (fun i s => c i s * I i s)
    (fun i s => c i s * R i s) Λ A (fun _ => 1) ?_ ?_ ?_
  · intro i _ s hs
    rw [hRelation i s hs, mul_assoc]
  · intro s hs
    simpa only [one_mul] using hsum s hs
  · intro i hi a b ε hε
    obtain ⟨B, hB⟩ := hc i hi a b ε hε
    obtain ⟨C, hC⟩ := hBound i a b ε hε
    refine ⟨max B 0 * max C 0, fun s ha hb h₀ h₁ => ?_⟩
    rw [norm_mul]
    exact mul_le_mul ((hB s ha hb h₀ h₁).trans (le_max_left _ _))
      ((hC s ha hb h₀ h₁).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

end Langlands.Global.CuspidalPairPoles
