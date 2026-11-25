/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.AlternatingCechPartialSortUnique
import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section
set_option autoImplicit false
universe v
namespace AlgebraicGeometry.Scheme

private abbrev PrefixOutgoing {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    (cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      x.2.2.2.val < x.2.1.val}

private abbrev PrefixIncoming {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
    (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
      (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
        y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}

private def deletePerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1))
    (e : Fin n ≃ {i : Fin (n + 1) // i ≠ k} := finSuccAboveEquiv k) :
    Equiv.Perm (Fin n) :=
  e.trans
    ((σ.subtypeEquiv (p := fun i ↦ i ≠ k) (q := fun j ↦ j ≠ σ k)
      (fun _ ↦ σ.injective.ne_iff.symm)).trans (finSuccAboveEquiv (σ k)).symm)

-- The source complement enumeration need not be increasing.
private theorem deletePerm_spec {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) (z : Fin n)
    (e : Fin n ≃ {i : Fin (n + 1) // i ≠ k} := finSuccAboveEquiv k) :
    (σ k).succAbove (deletePerm σ k e z) = σ (e z).val := by
  have h := (finSuccAboveEquiv (σ k)).apply_symm_apply
    ((σ.subtypeEquiv (p := fun i ↦ i ≠ k) (q := fun j ↦ j ≠ σ k)
      (fun _ ↦ σ.injective.ne_iff.symm)) (e z))
  exact congrArg Subtype.val h

-- Stable sorting is preserved by any increasing restriction square.
private theorem stable_restrict {I : Type v} [LinearOrder I] {m n : ℕ}
    (t : Fin m → I) (σ : Equiv.Perm (Fin m)) (ρ : Equiv.Perm (Fin n))
    (d e : Fin n → Fin m) (hd : StrictMono d) (he : StrictMono e)
    (hs : cechStableSort t σ) (h : ∀ z, e (ρ z) = σ (d z)) :
    cechStableSort (t ∘ e) ρ := by
  constructor
  · intro i j hij
    change t (e (ρ i)) ≤ t (e (ρ j))
    rw [h, h]
    exact hs.1 (hd.monotone hij)
  · intro i j hij ht
    apply he.lt_iff_lt.mp
    rw [h, h]
    apply hs.2 _ _ (hd hij)
    simpa only [Function.comp_apply, h] using ht

-- The lexicographic criterion works on arbitrary linearly ordered position/label types.
private theorem stable_compare {J K I : Type*} [LinearOrder J] [LinearOrder K]
    [LinearOrder I] (t : K → I) (f : J → K) (hm : Monotone (t ∘ f))
    (htie : ∀ i j, i < j → t (f i) = t (f j) → f i < f j) (i j : J) :
    i < j ↔ t (f i) < t (f j) ∨ (t (f i) = t (f j) ∧ f i < f j) := by
  constructor
  · intro hij
    rcases (hm hij.le).lt_or_eq with ht | ht
    · exact Or.inl ht
    · exact Or.inr ⟨ht, htie i j hij ht⟩
  · intro h
    by_contra hn
    have hji : j ≤ i := le_of_not_gt hn
    rcases hji.eq_or_lt with he | hl
    · subst i
      rcases h with h | ⟨_, h⟩ <;> exact (lt_irrefl _ h)
    · have ht := hm hl.le
      rcases h with h | ⟨he, h⟩
      · exact (not_lt_of_ge ht h)
      · exact (not_lt_of_ge (htie j i hl he.symm).le h)

private theorem partial_delete_prefix {n : ℕ} (σ τ : Equiv.Perm (Fin (n + 1)))
    (a r : Fin (n + 1)) (b : Fin n) (ht : cechPartialSort σ τ a)
    (hb : a.val = b.val + 1) (hr : r.val < a.val) :
    cechPartialSort (deletePerm σ r) (deletePerm τ r) b := by
  have hj : τ r = σ r := ht.1 r hr
  constructor
  · intro i hi
    apply (Fin.strictMono_succAbove (σ r)).injective
    rw [deletePerm_spec σ r i, ← hj, deletePerm_spec τ r i]
    simp only [finSuccAboveEquiv_apply]
    apply ht.1
    simp only [Fin.succAbove]
    split <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
  · intro i j hi hij
    apply (Fin.strictMono_succAbove (τ r)).lt_iff_lt.mp
    rw [deletePerm_spec, deletePerm_spec]
    simp only [finSuccAboveEquiv_apply]
    apply ht.2 _ _ ?_ ((Fin.strictMono_succAbove r) hij)
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      change r.val ≤ i.val
      omega)]
    simp only [Fin.val_succ]
    omega

private def prefix_delete {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : PrefixOutgoing p t) : PrefixIncoming p t := by
  let σ := x.val.1
  let a := x.val.2.1
  let τ := x.val.2.2.1
  let r : Fin (p + 2) := ⟨x.val.2.2.2.val, by
    have := x.property.2
    have := a.isLt
    omega⟩
  have hr : r.val < a.val := x.property.2
  let b : Fin (p + 1) := ⟨a.val - 1, by have := a.isLt; omega⟩
  have hb : a.val = b.val + 1 := by dsimp only [b]; omega
  let j := σ r
  let ρ := deletePerm σ r
  let η := deletePerm τ r
  refine ⟨(j, ρ, b, η), ⟨?_, ?_⟩, ?_⟩
  · exact stable_restrict t σ ρ r.succAbove (σ r).succAbove
      (Fin.strictMono_succAbove r) (Fin.strictMono_succAbove (σ r))
      x.property.1.1 (fun z ↦ by
        simpa only [finSuccAboveEquiv_apply] using deletePerm_spec σ r z)
  · exact partial_delete_prefix σ τ a r b x.property.1.2 hb hr
  · have hra : r.succAbove b = a := by
      rw [Fin.succAbove_of_le_castSucc _ _ (by
        change r.val ≤ b.val
        omega)]
      exact Fin.ext hb.symm
    have hρ : j.succAbove (ρ b) = σ a := by
      simpa only [finSuccAboveEquiv_apply, hra] using deletePerm_spec σ r b
    rw [hρ]
    exact (stable_compare t σ x.property.1.1.1 x.property.1.1.2 r a).mp hr

private theorem prefix_delete_spec {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : PrefixOutgoing p t) :
    x.val.2.1.val = (prefix_delete p t x).val.2.2.1.val + 1 ∧
    ∃ hr : x.val.2.2.2.val < p + 2,
      x.val.2.2.1 ⟨x.val.2.2.2.val, hr⟩ = (prefix_delete p t x).val.1 := by
  have hr := x.property.2
  have ha := x.val.2.1.isLt
  refine ⟨?_, by omega, ?_⟩
  · change x.val.2.1.val = x.val.2.1.val - 1 + 1
    omega
  · exact x.property.1.2.1 _ hr

private theorem prefix_delete_injective {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) : Function.Injective (prefix_delete p t) := by
  intro x x' he
  obtain ⟨ha, hr, hj⟩ := prefix_delete_spec p t x
  obtain ⟨ha', hr', hj'⟩ := prefix_delete_spec p t x'
  have hσ : x.val.1 = x'.val.1 :=
    (Tuple.eq_sort_iff.mpr x.property.1.1).trans
      (Tuple.eq_sort_iff.mpr x'.property.1.1).symm
  have hav : x.val.2.1.val = x'.val.2.1.val := by
    rw [ha, ha', he]
  have haeq : x.val.2.1 = x'.val.2.1 := Fin.ext hav
  have hτ : x.val.2.2.1 = x'.val.2.2.1 := by
    apply (cechPartialSort_existsUnique (p + 2) x.val.1 x.val.2.1.val
      x.val.2.1.isLt.le).unique x.property.1.2
    simpa only [cechPartialSort, hσ, haeq] using x'.property.1.2
  have hrr : (⟨x.val.2.2.2.val, hr⟩ : Fin (p + 2)) = ⟨x'.val.2.2.2.val, hr'⟩ := by
    apply x.val.2.2.1.injective
    rw [hj, hτ, hj', he]
  have hrval := congrArg Fin.val hrr
  apply Subtype.ext
  exact Prod.ext hσ (Prod.ext haeq (Prod.ext hτ (Fin.ext hrval)))

private theorem prefix_delete_surjective {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) : Function.Surjective (prefix_delete p t) := by
  intro y
  let j := y.val.1
  let ρ := y.val.2.1
  let b := y.val.2.2.1
  let η := y.val.2.2.2
  let σ := Tuple.sort t
  have hs : cechStableSort t σ := Tuple.eq_sort_iff.mp rfl
  let r := σ.symm j
  have hrj : σ r = j := σ.apply_symm_apply j
  have hρ : deletePerm σ r = ρ := by
    apply (Tuple.eq_sort_iff.mpr ?_).trans
      (Tuple.eq_sort_iff.mpr y.property.1.1).symm
    simpa only [cechStableSort, hrj] using
      stable_restrict t σ (deletePerm σ r) r.succAbove (σ r).succAbove
        (Fin.strictMono_succAbove r) (Fin.strictMono_succAbove (σ r))
        hs (fun z ↦ by
          simpa only [finSuccAboveEquiv_apply] using deletePerm_spec σ r z)
  have hdel : σ (r.succAbove b) = j.succAbove (ρ b) := by
    simpa only [finSuccAboveEquiv_apply, hrj, hρ] using (deletePerm_spec σ r b).symm
  have hrb : r.val ≤ b.val := by
    have hlt : r < r.succAbove b := (stable_compare t σ hs.1 hs.2 r (r.succAbove b)).mpr (by
      simpa only [hrj, hdel] using y.property.2)
    by_contra hn
    rw [Fin.succAbove_of_castSucc_lt _ _ (by exact lt_of_not_ge hn)] at hlt
    change r.val < b.val at hlt
    omega
  let a : Fin (p + 2) := b.succ
  have hra : r.val < a.val := by change r.val < b.val + 1; omega
  obtain ⟨τ, ht, _⟩ := cechPartialSort_existsUnique (p + 2) σ a.val (by omega)
  have hη : deletePerm τ r = η := by
    apply (cechPartialSort_existsUnique (p + 1) ρ b.val b.isLt.le).unique
      ?_ y.property.1.2
    rw [← hρ]
    exact partial_delete_prefix σ τ a r b ht rfl hra
  let x : PrefixOutgoing p t :=
    ⟨(σ, a, τ, r.castSucc), ⟨hs, ht⟩, hra⟩
  refine ⟨x, ?_⟩
  have hx : (⟨x.val.2.2.2.val, by have := r.isLt; exact this⟩ : Fin (p + 2)) = r := rfl
  apply Subtype.ext
  change (prefix_delete p t x).val = (j, ρ, b, η)
  dsimp only [prefix_delete]
  simp only [hx]
  dsimp only [x]
  change (σ r, deletePerm σ r, (⟨a.val - 1, _⟩ : Fin (p + 1)),
    deletePerm τ r) = (j, ρ, b, η)
  rw [hrj, hρ, hη]
  congr 2

/-- Existence of the prefix-deletion equivalence, with its index and junction facts.
Source: Stacks Project, Tag 01FM, prefix-deletion correspondence.
Proof: Write n=p+2. For an outgoing (σ,a,τ,r), the inequality r<a<n
makes r a position of both permutations and forces a≥1. Prefix agreement gives
j=σ(r)=τ(r). Restrict σ and τ to the complements of position r and label j,
using the increasing bijections r.succAbove and j.succAbove to renumber them,
and put b=a-1. The resulting permutations ρ and η are genuine bijections:
σ and τ restrict to bijections of these complements. Increasing renumbering
preserves the stable order of the pairs (t(k),k), hence ρ is stably sorted.
For k<b, r.succAbove(k)<a, so the two restricted prefixes agree. For b≤k<l,
a≤r.succAbove(k)<r.succAbove(l); thus the restricted tail of η increases.
The entry of ρ at b came from position a of σ. Since r<a, its pair follows
(t(j),j), giving exactly the incoming before condition.
Conversely, for incoming (j,ρ,b,η), let r be the number of labels whose pair
(t(k),k) precedes (t(j),j). The before condition says r≤b. Insert j at position r
into both permutations j.succAbove∘ρ and j.succAbove∘η, and put a=b+1<n.
The first permutation is stably sorted. Before a, the second agrees with it:
the inserted position agrees, and the other positions correspond to k<b.
Starting at a, positions correspond to k≥b, so the second tail increases.
These are permutations because insertion restores exactly the missing label.
Deletion followed by insertion restores the original permutations because the
stable order fixes the unique rank r; insertion followed by deletion restores
the two smaller permutations. The prefix lengths also recover each other.
Thus the maps are inverse and define the required equivalence. By construction
a=b+1 and τ(r)=j. For p=0 the smaller permutations are identities; the argument
also includes b=0 and b=p. Equal t-values use the original label as tie breaker;
an empty I admits no input tuple.
(blueprint: new-prefix-deletion-existence) -/
theorem prefixDeletionExistence {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : ({x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    (cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      x.2.2.2.val < x.2.1.val}) ≃
      ({y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
    (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
      (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
        y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}), ∀ x,
      let y := e x
      x.1.2.1.val = y.1.2.2.1.val + 1 ∧
      ∃ hr : x.1.2.2.2.val < p + 2,
        x.1.2.2.1 ⟨x.1.2.2.2.val, hr⟩ = y.1.1 := by
  classical
  let e := Equiv.ofBijective (prefix_delete p t)
    ⟨prefix_delete_injective p t, prefix_delete_surjective p t⟩
  exact ⟨e, prefix_delete_spec p t⟩

end AlgebraicGeometry.Scheme
