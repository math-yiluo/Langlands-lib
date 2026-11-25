/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingJunctionDeletions
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingNonjunctionCancellation

/-!
# The uncancelled junction terms in the first Čech sorting homotopy

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-first-sorting-boundary)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open Classical in
/-- After pairing nonjunction deletions, the two differential expansions leave
consecutive signed partial sorting stages. This statement does not identify the
endpoints or telescope the sum.

Source: Stacks 01FM, verification of equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-first-sorting-boundary)

Proof: Label each entry by its original position, including equal values. The stable
sort filter has exactly one solution, as in `Tuple.eq_sort_iff`. At each prefix length,
the partial sort filter also has exactly one solution: fix the prefix and list the
unused labels increasingly. Expand both differentials and distribute through the
finite sums and integer multiples. In the outgoing expansion, pair a deletion of a
label different from the repeated junction label with the incoming term for the
same deleted original position. Deleting in the prefix reduces its length by one;
deleting in the tail preserves it. The remaining sorting permutations are those of
the corresponding face, since deleting a labelled entry preserves lexicographic
order. Deleting position r with value label j changes the permutation sign by
(-1)^(r+j): move that position and value to the end and restrict the permutation.
Together with the differential and junction signs, this gives opposite coefficients
for each paired term. Index maps have identical composites with all projections,
so their transports agree by the product universal property. The two unpaired
occurrences of the junction label have the signed partial permutation with prefix
length a and the negative of that with prefix length a+1. Summing these gives the
displayed sum. The last two partial stages are identical, so the terminal summand
is zero. No telescoping or identification of the first and final stages is needed.
This argument uses labels rather than distinct values and thus includes tuples
with repetitions. If the index type is empty there is no tuple to evaluate. -/
theorem cechFirstSortingBoundary (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) :
    let B : ℕ → S.cochains F (p + 1) := fun a t ↦
      ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ τ : Equiv.Perm (Fin (p + 2)),
        if cechStableSort t σ ∧
            (∀ k, k.val < a → τ k = σ k) ∧
            (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
          (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0
    (cechFirstSortingHom X U F S (p + 1) (S.differential F (p + 1) s)) t +
      (S.differential F p (cechFirstSortingHom X U F S p s)) t =
        ∑ a : Fin (p + 2), (B a.val t - B (a.val + 1) t) := by
  classical
  dsimp only
  let E := fun (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
      (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) ↦
    ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
      F.map (S.indexMap t (cechJunction σ τ a)).op
        ((-1 : ℤ) ^ r.val •
          F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
            (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove)))
  let J := (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
    ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a then E σ a τ r else 0)
  let N := (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
    ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r ≠ σ a then E σ a τ r else 0)
  have hJ := cechFirstSortingJunctionDeletions X U F S p s t
  have hN := cechFirstSortingNonjunctionCancellation X U F S p s t
  change J = _ at hJ
  change N + (S.differential F p (cechFirstSortingHom X U F S p s)) t = 0 at hN
  have hd : (cechFirstSortingHom X U F S (p + 1)
      (S.differential F (p + 1) s)) t = J + N := by
    change (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)),
        if cechStableSort t σ ∧ cechPartialSort σ τ a then
          ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
            F.map (S.indexMap t (cechJunction σ τ a)).op
              (S.differentialValue F (p + 1) s (t ∘ cechJunction σ τ a))
        else 0) = J + N
    dsimp only [J, N, E]
    simp only [SiteCechComplex.differentialValue, map_sum, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases h : cechStableSort t σ ∧ cechPartialSort σ τ a
    · simp only [h, true_and, ite_true]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : cechJunction σ τ a r = σ a <;> simp [hr]
    · simp [h]
  rw [hd, add_assoc, hN, add_zero, hJ]


end AlgebraicGeometry.Scheme
