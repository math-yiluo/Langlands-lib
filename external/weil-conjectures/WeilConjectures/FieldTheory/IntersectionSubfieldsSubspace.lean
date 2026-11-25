/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Nonzero intersections of a subspace with a directed family of subfields

Source: Stacks Project, More on Algebra, Lemma 15.47.3, Tag 07P3
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v w

namespace IntermediateField

/-- For a nonempty downward directed family of intermediate fields whose intersection is the
base field, a linear subspace of `Kⁿ` contains a nonzero vector over the base field exactly when
it contains a nonzero vector over every field of the family.

Source: Stacks Project, More on Algebra, Lemma 15.47.3, Tag 07P3
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof:
1. A nonzero vector over `k` lies over every intermediate field, giving the forward implication.
2. For the converse, induct on `n`. For `n = 1`, a nonzero vector in the subspace makes the
   subspace all of `K`. Nonemptiness of the index type supplies such a vector, so `1` works.
3. For larger `n`, let `W` be the subspace of tails of vectors in `V` with first coordinate zero.
   A nonzero vector of `W` over `k` finishes the proof by adjoining a leading zero. Otherwise,
   the induction hypothesis gives an index `a` for which `W` has zero intersection over `L a`.
4. Choose a nonzero vector of `V` over `L a`. Its first coordinate is nonzero, so divide by it
   to obtain `v` with first coordinate `1`. Subtracting the first coordinate times `v` from
   any vector of `V` over `L a` shows that this intersection is the line `(L a) v`.
   For any `L b ≤ L a`, a nonzero vector over `L b` therefore normalizes to the same `v`,
   so all coordinates of `v` lie in `L b`.
5. For any index `c`, downward directedness supplies `b` with `L b ≤ L a ⊓ L c`.
   Thus every coordinate of `v` lies in every `L c`, hence in their intersection `k`.
   Its first coordinate is `1`, so it is the required nonzero vector. -/
theorem exists_ne_zero_mem_base_iff_forall_mem_intermediateField
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {ι : Type w} [Nonempty ι] (L : ι → IntermediateField k K)
    (h_inter : (⨅ a, L a) = ⊥)
    (h_directed : ∀ a b : ι, ∃ c : ι, L c ≤ L a ⊓ L b)
    (n : ℕ) (hn : 1 ≤ n) (V : Submodule K (Fin n → K)) :
    (∃ x : Fin n → K, x ∈ V ∧ x ≠ 0 ∧ ∀ i, x i ∈ (⊥ : IntermediateField k K)) ↔
      ∀ a : ι, ∃ x : Fin n → K, x ∈ V ∧ x ≠ 0 ∧ ∀ i, x i ∈ L a := by
  classical
  constructor
  · rintro ⟨x, hx, hne, hbase⟩ a
    exact ⟨x, hx, hne, fun i => (bot_le : (⊥ : IntermediateField k K) ≤ L a) (hbase i)⟩
  · intro h
    have descent : ∀ m : ℕ, ∀ U : Submodule K (Fin m → K),
        (∀ a : ι, ∃ x : Fin m → K, x ∈ U ∧ x ≠ 0 ∧ ∀ i, x i ∈ L a) →
        ∃ x : Fin m → K, x ∈ U ∧ x ≠ 0 ∧
          ∀ i, x i ∈ (⊥ : IntermediateField k K) := by
      intro m
      induction m with
      | zero =>
        intro U hall
        obtain ⟨x, _, hne, _⟩ := hall (Classical.arbitrary ι)
        exact (hne (Subsingleton.elim _ _)).elim
      | succ m ih =>
        intro U hall
        let insertZero : (Fin m → K) →ₗ[K] (Fin (m + 1) → K) :=
          { toFun := fun y => Fin.cons (0 : K) y
            map_add' := by
              intro x y
              ext i
              refine Fin.cases ?_ (fun j => ?_) i <;> simp
            map_smul' := by
              intro c x
              ext i
              refine Fin.cases ?_ (fun j => ?_) i <;> simp }
        let W := U.comap insertZero
        by_cases hW : ∃ y : Fin m → K, y ∈ W ∧ y ≠ 0 ∧
            ∀ i, y i ∈ (⊥ : IntermediateField k K)
        · obtain ⟨y, hy, hyne, hybase⟩ := hW
          refine ⟨insertZero y, hy, ?_, ?_⟩
          · intro heq
            apply hyne
            ext i
            exact congrFun heq i.succ
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact (⊥ : IntermediateField k K).zero_mem
            · exact hybase j
        · have hfail : ¬ ∀ a : ι, ∃ y : Fin m → K,
              y ∈ W ∧ y ≠ 0 ∧ ∀ i, y i ∈ L a := fun hw => hW (ih W hw)
          obtain ⟨a, ha⟩ := not_forall.mp hfail
          have zero_of_head_zero : ∀ z : Fin (m + 1) → K,
              z ∈ U → (∀ i, z i ∈ L a) → z 0 = 0 → z = 0 := by
            intro z hz hzfield hz0
            have htail : Fin.tail z ∈ W := by
              change Fin.cons 0 (Fin.tail z) ∈ U
              rw [← hz0, Fin.cons_self_tail]
              exact hz
            have htail0 : Fin.tail z = 0 := by
              by_contra hne
              exact ha ⟨Fin.tail z, htail, hne, fun i => hzfield i.succ⟩
            ext i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact hz0
            · exact congrFun htail0 j
          obtain ⟨x, hx, hxne, hxfield⟩ := hall a
          have hx0 : x 0 ≠ 0 := by
            intro hx0
            exact hxne (zero_of_head_zero x hx hxfield hx0)
          let v : Fin (m + 1) → K := (x 0)⁻¹ • x
          have hv : v ∈ U := U.smul_mem _ hx
          have hvfield : ∀ i, v i ∈ L a :=
            fun i => (L a).mul_mem ((L a).inv_mem (hxfield 0)) (hxfield i)
          have hv0 : v 0 = 1 := by
            change (x 0)⁻¹ * x 0 = 1
            exact inv_mul_cancel₀ hx0
          have normalized_unique : ∀ z : Fin (m + 1) → K,
              z ∈ U → (∀ i, z i ∈ L a) → z 0 = 1 → z = v := by
            intro z hz hzfield hz0
            have hsub : z - v = 0 := zero_of_head_zero (z - v)
              (U.sub_mem hz hv) (fun i => (L a).sub_mem (hzfield i) (hvfield i))
              (by simp [hz0, hv0])
            exact sub_eq_zero.mp hsub
          refine ⟨v, hv, ?_, ?_⟩
          · intro heq
            have : (0 : K) = 1 := (congrFun heq 0).symm.trans hv0
            exact zero_ne_one this
          · intro i
            rw [← h_inter]
            simp only [← SetLike.mem_coe, coe_iInf, Set.mem_iInter]
            intro b
            obtain ⟨c, hc⟩ := h_directed a b
            obtain ⟨z, hz, hzne, hzfield⟩ := hall c
            have hzfielda : ∀ j, z j ∈ L a := fun j => (le_inf_iff.mp hc).1 (hzfield j)
            have hz0 : z 0 ≠ 0 := by
              intro hz0
              exact hzne (zero_of_head_zero z hz hzfielda hz0)
            have hnorm : (z 0)⁻¹ • z = v := normalized_unique _
              (U.smul_mem _ hz)
              (fun j => (L a).mul_mem ((L a).inv_mem (hzfielda 0)) (hzfielda j))
              (inv_mul_cancel₀ hz0)
            rw [← hnorm]
            exact (le_inf_iff.mp hc).2
              ((L c).mul_mem ((L c).inv_mem (hzfield 0)) (hzfield i))
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
    exact descent (m + 1) V h

end IntermediateField
