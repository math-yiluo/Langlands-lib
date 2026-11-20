import Langlands.Global.Factors.IsobaricArchimedeanQuotients
import Langlands.Representation.Archimedean.ComplexStandardLanglandsQuotientProof
import Langlands.Representation.Archimedean.ComplexStrictSwapNonvanishing
import Langlands.Representation.Archimedean.ComplexTransposePairingReduction
import Langlands.Representation.Archimedean.StandardQuotientFactorization

/-!
# The complex Langlands quotient in the original induction order

The ordered standard module maps through the standard module in the supplied order
to the reverse-ordered standard module with nonzero composite. Stable sorting
gives the strict steps, and the injective comparison of ascending sorted lists
accounts for equal real exponents at the end. The kernel of the composite is
the kernel of the Langlands quotient map.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix.Norms.Operator

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open ComplexSwapJacquet
open Langlands.LocalFactor.Archimedean (ComplexCharacterData StrictAdjacentSwap
  strictAdjacentSwaps_mergeSort complexStrictAdjacentSwaps_mergeSort)
open Langlands.Automorphic (complexStandardKFinite)

local notation "Standard(" n ", " ds ")" => complexStandardKFinite n ds

private theorem exists_strictSwapChain {n : ℕ} {xs ys : List ComplexCharacterData}
    (hn : xs.length = n)
    (h : Relation.ReflTransGen (StrictAdjacentSwap (fun d => -d.exponent.re)) xs ys) :
    ys.length = n ∧ ∃ m, Nonempty (StrictSwapChain n xs ys m) := by
  induction h with
  | refl => exact ⟨hn, 0, ⟨.nil xs⟩⟩
  | tail _ hstep ih =>
    obtain ⟨hlen, m, ⟨w⟩⟩ := ih
    have hlen' := hstep.perm.length_eq.symm.trans hlen
    obtain ⟨pre, post, a, b, hlt, rfl, rfl⟩ := hstep
    have hsize : pre.length + (post.length + 2) = n := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
    let i : Fin n := ⟨pre.length, by omega⟩
    let j : Fin n := ⟨pre.length + 1, by omega⟩
    have hpos : 0 < (a.exponent - b.exponent).re :=
      sub_pos.mpr (neg_lt_neg_iff.mp hlt)
    let step : StrictSwapChain n (pre ++ a :: b :: post) (pre ++ b :: a :: post) 1 :=
      .cons pre post a b hlen i j rfl rfl hpos (.nil _)
    exact ⟨hlen', 1 + m, ⟨w.append step⟩⟩

private theorem reverse_complexStrictAdjacentSwaps_mergeSort (xs : List ComplexCharacterData) :
    Relation.ReflTransGen (StrictAdjacentSwap (fun d => -d.exponent.re))
      (xs.mergeSort complexLanglandsLE) xs := by
  refine Relation.ReflTransGen.mono ?_ _ _
    (Relation.ReflTransGen.swap _ _ (complexStrictAdjacentSwaps_mergeSort xs))
  intro as bs h
  obtain ⟨pre, post, a, b, hlt, rfl, rfl⟩ := h
  exact ⟨pre, post, b, a, neg_lt_neg hlt, rfl, rfl⟩

/-- The reverse intertwiner for the stably ordered complex list factors through
the standard module of the original list, with nonzero composite. -/
def ComplexOrderFactorizationStatement : Prop :=
  ∀ (n : ℕ) (xs : List ComplexCharacterData), xs.length = n →
    let ds := xs.mergeSort complexLanglandsLE
    ∃ (A : Standard(n, ds) →ₗ[ℂ] Standard(n, xs))
      (B : Standard(n, xs) →ₗ[ℂ] Standard(n, ds.reverse)),
      IsComplexStandardIntertwining n (complexStandardRep n xs) (complexStandardLie n xs) ds A ∧
      IsComplexStandardIntertwining n (complexStandardRep n ds.reverse)
        (complexStandardLie n ds.reverse) xs B ∧ B ∘ₗ A ≠ 0

theorem complexOrderFactorization : ComplexOrderFactorizationStatement := by
  intro n xs hx
  let ds := xs.mergeSort complexLanglandsLE
  let fs := xs.mergeSort (fun a b => decide (-(b.exponent.re) ≤ -(a.exponent.re)))
  have hds : ds.Perm xs := List.mergeSort_perm _ _
  have hfs : fs.Perm xs := List.mergeSort_perm _ _
  have hn : ds.length = n := hds.length_eq.trans hx
  have ho : IsComplexLanglandsOrdered ds := isComplexLanglandsOrdered_mergeSort xs
  obtain ⟨_, _, ⟨w⟩⟩ := exists_strictSwapChain hn
    (reverse_complexStrictAdjacentSwaps_mergeSort xs)
  have htofs : Relation.ReflTransGen (StrictAdjacentSwap (fun d => -d.exponent.re)) xs fs :=
    strictAdjacentSwaps_mergeSort (fun d => -d.exponent.re) xs
  obtain ⟨hfn, _, ⟨v⟩⟩ := exists_strictSwapChain hx htofs
  have hvw : v.intertwiner ∘ₗ w.intertwiner ≠ 0 := by
    rw [← w.intertwiner_append v]
    exact (w.append v).intertwiner_ne_zero hn ho
  have hsorted : fs.Pairwise (fun a b => a.exponent.re ≤ b.exponent.re) := by
    have h := List.pairwise_mergeSort
      (le := fun a b : ComplexCharacterData => decide (-(b.exponent.re) ≤ -(a.exponent.re)))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq, neg_le_neg_iff] at hab hbc ⊢
        exact hab.trans hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq, neg_le_neg_iff]
        exact le_total _ _) xs
    exact h.imp (by simp)
  have hrev : ds.reverse.Pairwise (fun a b => a.exponent.re ≤ b.exponent.re) := by
    simpa only [List.pairwise_reverse, IsComplexLanglandsOrdered] using ho
  have hperm : fs.Perm ds.reverse := hfs.trans (hds.symm.trans (List.reverse_perm ds).symm)
  have he := ComplexTransposePairingReduction.injectiveIntertwiner_sorted_perm n
    fs ds.reverse hperm hsorted hrev [] (by simpa using hfn)
  simp only [List.nil_append] at he
  obtain ⟨E, hEinj, hE⟩ := he
  refine ⟨w.intertwiner, E ∘ₗ v.intertwiner, w.isComplexStandardIntertwining,
    v.isComplexStandardIntertwining.comp E hE.map_complexStandardRep
      (fun X f => hE.map_complexStandardLie (1 ⊗ₜ X) f), ?_⟩
  intro h
  apply hvw
  ext f : 1
  apply hEinj
  simpa using LinearMap.congr_fun h f

/-- The actual complex Langlands quotient of the stably ordered list occurs
as the quotient of a stable subspace in the original induction order. -/
theorem complexOrderedQuotient_subquotient (n : ℕ) (xs : List ComplexCharacterData)
    (hx : xs.length = n) :
    let ds := xs.mergeSort complexLanglandsLE
    ∃ (R : Submodule ℂ Standard(n, ds))
      (hR : IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) R),
      IsIrreducibleGKModule ((complexStandardRep n ds).quotient R hR.1)
        (RealLeviDuality.quotLie (complexStandardLie n ds) R hR.2) ∧
      ∃ (W : Submodule ℂ Standard(n, xs))
        (hW : IsGKSubmodule (complexStandardRep n xs) (complexStandardLie n xs) W)
        (q : W →ₗ[ℂ] (Standard(n, ds) ⧸ R)),
        IsGKSubquotientMap ((complexStandardRep n ds).quotient R hR.1)
          (RealLeviDuality.quotLie (complexStandardLie n ds) R hR.2) hW q := by
  let ds := xs.mergeSort complexLanglandsLE
  have hn : ds.length = n := (List.mergeSort_perm xs _).length_eq.trans hx
  have ho : IsComplexLanglandsOrdered ds := isComplexLanglandsOrdered_mergeSort xs
  obtain ⟨R, hR, hproper, hmax⟩ := complexStandardLanglandsQuotient n ds hn ho
  have hJ := isIrreducibleGKModule_quotient_of_largest hR hproper hmax
  have hp : IsComplexStandardIntertwining n ((complexStandardRep n ds).quotient R hR.1)
      (RealLeviDuality.quotLie (complexStandardLie n ds) R hR.2) ds R.mkQ := by
    exact isComplexStandardIntertwining_id n ds |>.comp R.mkQ (fun _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨A, B, hA, hB, hne⟩ := complexOrderFactorization n xs hx
  obtain ⟨hW, q, hq, _⟩ :=
    complexStandardQuotient_of_reverse_factorization hn ho hJ R.mkQ_surjective hp hA hB hne
  exact ⟨R, hR, hJ, LinearMap.range A, hW, q, hq⟩

end Langlands.Archimedean
