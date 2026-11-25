/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Invariants of `p`-groups on `𝔽_p`-vector spaces

Let `G` be a `p`-group and `V` a finite-dimensional `𝔽_p`-linear representation of `G`. Then:

* if `V ≠ 0`, the invariants `V^G` are nonzero: the number of fixed points of the action of `G`
  on the finite set `V` is congruent to `|V| = p ^ dim V ≡ 0` modulo `p`, and `0` is one of them;
* `V` has a `G`-stable flag `0 = F₀ < F₁ < ⋯ < F_n = V`, `n = dim V`, with `dim F_i = i`, on
  whose successive quotients `G` acts trivially. Each step applies the first point to the
  quotient representation `V / F_i`.

## Main statements

- `Representation.invariants_ne_bot_of_isPGroup`: `V^G ≠ 0` for `V ≠ 0`.
- `Representation.exists_forall_sub_mem_of_isPGroup`: for a proper `G`-stable subspace `W`
  there is `x ∉ W` with `g x - x ∈ W` for all `g`.
- `Representation.invariants_ne_bot_and_exists_filtration_of_isPGroup`: both statements of
  the blueprint lemma together (blueprint: `lemma-reduction-unipotent-local-system--1`).
- `Representation.IsIrreducible.invariants_comp_subtype_eq_bot_or_eq_top`: in an irreducible
  representation the invariants of a normal subgroup are zero or everything.
-/

@[expose] public section

open Module

namespace Representation

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V] (ρ : Representation (ZMod p) G V)

/-- **The invariants of a `p`-group on a nonzero finite-dimensional `𝔽_p`-representation are
nonzero.** The fixed points of the action on the finite set `V`, of cardinality
`p ^ dim V`, are congruent to `|V| ≡ 0` modulo `p`; since `0` is fixed, so is some `x ≠ 0`. -/
theorem invariants_ne_bot_of_isPGroup (hG : IsPGroup p G) [Nontrivial V] :
    ρ.invariants ≠ ⊥ := by
  let : MulAction G V := MulAction.compHom V ρ
  have : Finite V := Module.finite_of_finite (ZMod p)
  have hdvd : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p Module.finrank_pos.ne'
  have h0 : (0 : V) ∈ MulAction.fixedPoints G V := fun g ↦ map_zero (ρ g)
  obtain ⟨x, hx, hx0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd h0
  rw [Submodule.ne_bot_iff]
  exact ⟨x, fun g ↦ hx g, hx0.symm⟩

/-- **A step of the `p`-group filtration**: for a proper `G`-stable subspace `W` of a
finite-dimensional `𝔽_p`-representation of a `p`-group `G`, there is `x ∉ W` such that
`g x - x ∈ W` for every `g`, i.e. whose class in `V / W` is invariant. This is
`Representation.invariants_ne_bot_of_isPGroup` for the quotient representation `V / W`. -/
theorem exists_forall_sub_mem_of_isPGroup (hG : IsPGroup p G) (W : Submodule (ZMod p) V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) (hne : W ≠ ⊤) :
    ∃ x ∉ W, ∀ g, ρ g x - x ∈ W := by
  have : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.2 hne
  obtain ⟨q, hq, hq0⟩ := Submodule.ne_bot_iff _ |>.1
    ((ρ.quotient W hW).invariants_ne_bot_of_isPGroup hG)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W q
  refine ⟨x, fun hx ↦ hq0 ((Submodule.Quotient.mk_eq_zero W).2 hx), fun g ↦ ?_⟩
  have := hq g
  rw [quotient_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at this
  exact this

/-- Extending a `G`-stable flag of length `k < dim V` by one step. -/
private theorem exists_flag_succ (hG : IsPGroup p G) (k : ℕ) (hk : k < finrank (ZMod p) V)
    (F : ℕ → Submodule (ZMod p) V) (h0 : F 0 = ⊥) (hk' : finrank (ZMod p) (F k) = k)
    (hstab : ∀ i ≤ k, ∀ g, F i ≤ (F i).comap (ρ g))
    (hstep : ∀ i < k, F i ≤ F (i + 1) ∧ finrank (ZMod p) (F (i + 1)) = i + 1 ∧
      ∀ g, ∀ x ∈ F (i + 1), ρ g x - x ∈ F i) :
    ∃ F' : ℕ → Submodule (ZMod p) V, F' 0 = ⊥ ∧ finrank (ZMod p) (F' (k + 1)) = k + 1 ∧
      (∀ i ≤ k + 1, ∀ g, F' i ≤ (F' i).comap (ρ g)) ∧
      ∀ i < k + 1, F' i ≤ F' (i + 1) ∧ finrank (ZMod p) (F' (i + 1)) = i + 1 ∧
        ∀ g, ∀ x ∈ F' (i + 1), ρ g x - x ∈ F' i := by
  have hne : F k ≠ ⊤ := by
    rintro h
    rw [h, finrank_top] at hk'
    omega
  obtain ⟨x, hx, hgx⟩ := ρ.exists_forall_sub_mem_of_isPGroup hG (F k) (hstab k le_rfl) hne
  set W := F k ⊔ Submodule.span (ZMod p) {x}
  have hWtriv (g : G) (y : V) (hy : y ∈ W) : ρ g y - y ∈ F k := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    have : ρ g (a + c • x) - (a + c • x) = (ρ g a - a) + c • (ρ g x - x) := by
      rw [map_add, map_smul, smul_sub]
      abel
    rw [this]
    exact add_mem (sub_mem (hstab k le_rfl g ha) ha) (Submodule.smul_mem _ _ (hgx g))
  obtain ⟨F', hle, hgt⟩ : ∃ F' : ℕ → Submodule (ZMod p) V,
      (∀ i ≤ k, F' i = F i) ∧ ∀ i, k < i → F' i = W :=
    ⟨fun i ↦ if i ≤ k then F i else W, fun i hi ↦ ite_eq_left hi,
      fun i hi ↦ ite_eq_right (by omega)⟩
  refine ⟨F', by rw [hle 0 (Nat.zero_le k), h0], ?_, ?_, ?_⟩
  · rw [hgt (k + 1) k.lt_succ_self, Submodule.finrank_sup_span_singleton hx, hk']
  · intro i hi g
    by_cases h : i ≤ k
    · rw [hle i h]
      exact hstab i h g
    · rw [hgt i (by omega)]
      intro y hy
      have := hWtriv g y hy
      rw [Submodule.mem_comap, ← sub_add_cancel (ρ g y) y]
      exact add_mem (le_sup_left (a := F k) this) hy
  · intro i hi
    by_cases hik : i + 1 ≤ k
    · rw [hle i (Nat.le_of_succ_le hik), hle (i + 1) hik]
      exact hstep i hik
    · obtain rfl : i = k := by omega
      rw [hle i le_rfl, hgt (i + 1) i.lt_succ_self]
      refine ⟨le_sup_left, ?_, fun g y hy ↦ hWtriv g y hy⟩
      rw [Submodule.finrank_sup_span_singleton hx, hk']

/-- **Representations of finite `p`-groups over `𝔽_p`.** Let `G` be a `p`-group and `V` a
finite-dimensional `𝔽_p`-linear representation of `G`. If `V ≠ 0` then `V^G ≠ 0`; and
(for any `V`) there is a flag `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = V`, `n = dim V`, of `G`-stable
subspaces with `dim F i = i` such that `G` acts trivially on each quotient
`F (i + 1) / F i`, i.e. `g x - x ∈ F i` for `x ∈ F (i + 1)`. Its successive quotients are thus
the trivial one-dimensional representation. The finiteness of `G` is not needed.
(blueprint: `lemma-reduction-unipotent-local-system--1`) -/
theorem invariants_ne_bot_and_exists_filtration_of_isPGroup (hG : IsPGroup p G) :
    (Nontrivial V → ρ.invariants ≠ ⊥) ∧
      ∃ F : ℕ → Submodule (ZMod p) V, F 0 = ⊥ ∧ F (finrank (ZMod p) V) = ⊤ ∧
        (∀ i ≤ finrank (ZMod p) V, ∀ g, F i ≤ (F i).comap (ρ g)) ∧
        ∀ i < finrank (ZMod p) V, F i ≤ F (i + 1) ∧ finrank (ZMod p) (F (i + 1)) = i + 1 ∧
          ∀ g, ∀ x ∈ F (i + 1), ρ g x - x ∈ F i := by
  refine ⟨fun _ ↦ ρ.invariants_ne_bot_of_isPGroup hG, ?_⟩
  have key (k : ℕ) (hk : k ≤ finrank (ZMod p) V) :
      ∃ F : ℕ → Submodule (ZMod p) V, F 0 = ⊥ ∧ finrank (ZMod p) (F k) = k ∧
        (∀ i ≤ k, ∀ g, F i ≤ (F i).comap (ρ g)) ∧
        ∀ i < k, F i ≤ F (i + 1) ∧ finrank (ZMod p) (F (i + 1)) = i + 1 ∧
          ∀ g, ∀ x ∈ F (i + 1), ρ g x - x ∈ F i := by
    induction k with
    | zero =>
      refine ⟨fun _ ↦ ⊥, rfl, finrank_bot _ _, fun _ _ _ ↦ bot_le, fun i hi ↦ ?_⟩
      omega
    | succ k ih =>
      obtain ⟨F, h0, hk', hstab, hstep⟩ := ih (by omega)
      exact ρ.exists_flag_succ hG k (by omega) F h0 hk' hstab hstep
  obtain ⟨F, h0, hn, hstab, hstep⟩ := key _ le_rfl
  exact ⟨F, h0, Submodule.eq_top_of_finrank_eq hn, hstab, hstep⟩

section Normal

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/-- In an irreducible representation the invariants `V^S` of a normal subgroup `S` are zero or
everything: they form a subrepresentation, since `s (g v) = g (g⁻¹ s g) v = g v` for `v ∈ V^S`
(`Representation.le_comap_invariants`). -/
theorem IsIrreducible.invariants_comp_subtype_eq_bot_or_eq_top [IsIrreducible ρ] :
    invariants (ρ.comp S.subtype) = ⊥ ∨ invariants (ρ.comp S.subtype) = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top (⟨invariants (ρ.comp S.subtype),
    fun g _ hv ↦ le_comap_invariants ρ S g hv⟩ : Subrepresentation ρ)).imp
      (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)

/-- A normal subgroup `S` with nonzero invariants in an irreducible representation acts
trivially. -/
theorem IsIrreducible.eq_one_of_invariants_ne_bot [IsIrreducible ρ]
    (h : invariants (ρ.comp S.subtype) ≠ ⊥) {s : G} (hs : s ∈ S) : ρ s = 1 := by
  have htop := (invariants_comp_subtype_eq_bot_or_eq_top ρ S).resolve_left h
  ext v
  have hv : v ∈ invariants (ρ.comp S.subtype) := htop ▸ Submodule.mem_top
  exact hv ⟨s, hs⟩

end Normal

end Representation
