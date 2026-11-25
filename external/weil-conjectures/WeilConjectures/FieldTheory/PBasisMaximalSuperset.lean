/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Zorn
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Maximal p-independent supersets

Source: Stacks Project, More on Algebra, Lemma Tag 07P2, third proof paragraph
(blueprint: lem-weil-pbc-p-independent-maximal-superset).
-/

@[expose] public section

universe u v

namespace FieldTheory

private noncomputable def supportedExponentEquiv {K : Type*} (p : ℕ)
    (hp : 0 < p) (S : Set K) :
    {E : S →₀ ℕ // ∀ a, E a < p} ≃
      {E : {E : K →₀ ℕ // ∀ a, E a < p} // (E.val.support : Set K) ⊆ S} := by
  classical
  refine
    { toFun := fun E ↦ ⟨⟨E.val.extendDomain, ?_⟩, Finsupp.support_extendDomain_subset _⟩
      invFun := fun E ↦ ⟨E.val.val.subtypeDomain (· ∈ S), fun a ↦ E.val.property a⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    by_cases ha : a ∈ S
    · simpa [Finsupp.extendDomain_apply, ha] using E.property ⟨a, ha⟩
    · simpa [Finsupp.extendDomain_apply, ha] using hp
  · intro E
    apply Subtype.ext
    exact Finsupp.subtypeDomain_extendDomain E.val
  · intro E
    apply Subtype.ext
    apply Subtype.ext
    exact Finsupp.extendDomain_subtypeDomain E.val.val (fun a ha ↦ E.property ha)

private theorem pIndependent_iff_supported
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) (S : Set K) :
    LinearIndependent (IntermediateField.adjoin k (Set.range (fun a : K ↦ a ^ p)))
      (fun E : {E : S →₀ ℕ // ∀ a, E a < p} ↦
        E.val.prod (fun a n ↦ (a : K) ^ n)) ↔
    LinearIndepOn (IntermediateField.adjoin k (Set.range (fun a : K ↦ a ^ p)))
      (fun E : {E : K →₀ ℕ // ∀ a, E a < p} ↦ E.val.prod (fun a n ↦ a ^ n))
      {E | (E.val.support : Set K) ⊆ S} := by
  classical
  apply linearIndependent_equiv' (supportedExponentEquiv p hp S)
  funext E
  dsimp [supportedExponentEquiv]
  rw [← Finsupp.prod_subtypeDomain_index
    (fun a ha ↦ Finsupp.support_extendDomain_subset E.val ha)]
  rw [Finsupp.subtypeDomain_extendDomain]
  rfl

/-- Every p-independent subset lies in a maximal p-independent subset.
Source: Stacks Project, More on Algebra, Definition Tag 07P1 and Lemma Tag 07P2,
third proof paragraph (blueprint: lem-weil-pbc-p-independent-maximal-superset).

Proof:
1. Order the p-independent subsets containing S by inclusion. S belongs to this order.
2. For a nonempty chain, take its union. A finite relation among bounded monomials
   uses only finitely many generators. Successive comparison in the chain puts all
   these generators in a single member. Restrict the exponent functions to that member;
   they retain their products and remain distinct. Its independence kills the relation.
   For the empty chain take S itself as upper bound.
3. Apply zorn_subset to this order. The resulting T is maximal even among all
   p-independent subsets, since every superset of T still contains S.
-/
theorem exists_maximal_pIndependent_superset
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP K p]
    (S : Set K)
    (hS : LinearIndependent
      (IntermediateField.adjoin k (Set.range (fun a : K ↦ a ^ p)))
      (fun E : {E : S →₀ ℕ // ∀ s : S, E s < p} ↦
        E.val.prod (fun s e ↦ (s : K) ^ e))) :
    ∃ T : Set K, S ⊆ T ∧ Maximal (fun T : Set K ↦ LinearIndependent
      (IntermediateField.adjoin k (Set.range (fun a : K ↦ a ^ p)))
      (fun E : {E : T →₀ ℕ // ∀ t : T, E t < p} ↦
        E.val.prod (fun t e ↦ (t : K) ^ e))) T := by
  classical
  let F := IntermediateField.adjoin k (Set.range (fun a : K ↦ a ^ p))
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let B := {E : K →₀ ℕ // ∀ a, E a < p}
  let m : B → K := fun E ↦ E.val.prod (fun a n ↦ a ^ n)
  let D : Set K → Set B := fun T ↦ {E | (E.val.support : Set K) ⊆ T}
  have hmono : Monotone D := fun _ _ h E hE ↦ hE.trans h
  let P : Set K → Prop := fun T ↦ LinearIndepOn F m (D T)
  have hPS : P S := (pIndependent_iff_supported p hp S).mp hS
  have hchain : ∀ c ⊆ {T | S ⊆ T ∧ P T}, IsChain (· ⊆ ·) c →
      ∃ U ∈ {T | S ⊆ T ∧ P T}, ∀ T ∈ c, T ⊆ U := by
    intro c hc hcc
    by_cases hn : c.Nonempty
    · let U := ⋃₀ c
      have hD : D U = ⋃ T ∈ c, D T := by
        ext E
        constructor
        · intro hE
          obtain ⟨T, hTc, hET⟩ :=
            hcc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn
              (s := E.val.support) (by simpa [D, U, Set.sUnion_eq_biUnion] using hE)
          exact Set.mem_iUnion₂.mpr ⟨T, hTc, hET⟩
        · intro hE
          obtain ⟨T, hTc, hET⟩ := Set.mem_iUnion₂.mp hE
          exact hmono (Set.subset_sUnion_of_mem hTc) hET
      have hPU : P U := by
        dsimp [P]
        rw [hD]
        apply linearIndepOn_biUnion_of_directed
        · intro A hAc B hBc
          obtain ⟨T, hTc, hAT, hBT⟩ := hcc.directedOn A hAc B hBc
          exact ⟨T, hTc, hmono hAT, hmono hBT⟩
        · intro T hTc
          exact (hc hTc).2
      obtain ⟨T, hTc⟩ := hn
      exact ⟨U, ⟨(hc hTc).1.trans (Set.subset_sUnion_of_mem hTc), hPU⟩,
        fun T hTc ↦ Set.subset_sUnion_of_mem hTc⟩
    · exact ⟨S, ⟨Set.Subset.rfl, hPS⟩, fun T hTc ↦ (hn ⟨T, hTc⟩).elim⟩
  obtain ⟨T, hT⟩ := zorn_subset {T | S ⊆ T ∧ P T} hchain
  refine ⟨T, hT.prop.1, ?_⟩
  constructor
  · exact (pIndependent_iff_supported p hp T).mpr hT.prop.2
  · intro U hU hTU
    exact hT.2 ⟨hT.prop.1.trans hTU,
      (pIndependent_iff_supported p hp U).mp hU⟩ hTU

end FieldTheory
