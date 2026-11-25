/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.Filtration
public import Mathlib.Topology.Instances.Matrix
public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology

/-!
# `p`-adic pairings from compatible-free families of finite-level pairings

Let `A`, `B` be free `ℤ_p`-modules of finite rank with endomorphisms `F_A`, `F_B` and `c ∈ ℤ_p`.
Suppose that for every `m` there is a pairing `P : A × B ⟶ ℤ_p` which is a `c`-similitude
modulo `pᵐ`, `P(F_A x, F_B y) ≡ c P(x, y)`, and whose kernels modulo `pᵐ` are controlled by a
fixed power `pᵉ` (if `P(x, -) ≡ 0` then `pᵉ x ∈ pᵐ A`, and symmetrically). The pairings at the
different levels need not be compatible. Then there is a pairing `P : A × B ⟶ ℤ_p` which is an
exact `c`-similitude with trivial left and right kernels
(`LinearMap.exists_isSimilitude_of_forall_level`).

The proof is by compactness: in the compact space of matrices over `ℤ_p`, the pairings satisfying
the conditions at level `m` form a decreasing sequence of nonempty closed sets.

This is how the finite-level Poincaré dualities with coefficients `ℤ/ℓᵐ`, which need not be
compatible with each other, give an `ℓ`-adic Poincaré duality, hence one over `ℚ̄_ℓ`.
-/

@[expose] public section

open Topology

namespace LinearMap

variable {p : ℕ} [Fact p.Prime] {A B ι κ : Type*} [AddCommGroup A] [Module ℤ_[p] A]
  [AddCommGroup B] [Module ℤ_[p] B] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The pairings satisfying the conditions at level `m`: a `c`-similitude modulo `pᵐ` whose
kernels modulo `pᵐ` are killed by `pᵉ` modulo `pᵐ`. -/
def IsLevelSimilitude (FA : A →ₗ[ℤ_[p]] A) (FB : B →ₗ[ℤ_[p]] B) (c : ℤ_[p]) (e m : ℕ)
    (P : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p]) : Prop :=
  (∀ x y, P (FA x) (FB y) - c * P x y ∈ PadicInt.powOpenAddSubgroup p m) ∧
    (∀ x, (∀ y, P x y ∈ PadicInt.powOpenAddSubgroup p m) →
      ∃ x', (p : ℤ_[p]) ^ e • x = (p : ℤ_[p]) ^ m • x') ∧
    (∀ y, (∀ x, P x y ∈ PadicInt.powOpenAddSubgroup p m) →
      ∃ y', (p : ℤ_[p]) ^ e • y = (p : ℤ_[p]) ^ m • y')

private lemma isClosed_powOpenAddSubgroup (m : ℕ) :
    IsClosed (PadicInt.powOpenAddSubgroup p m : Set ℤ_[p]) :=
  (PadicInt.powOpenAddSubgroup p m).isClosed

private lemma isOpen_powOpenAddSubgroup (m : ℕ) :
    IsOpen (PadicInt.powOpenAddSubgroup p m : Set ℤ_[p]) :=
  (PadicInt.powOpenAddSubgroup p m).isOpen

private lemma mem_powOpenAddSubgroup_of_mul {m : ℕ} {z : ℤ_[p]}
    (hz : z ∈ PadicInt.powOpenAddSubgroup p m) (w : ℤ_[p]) :
    w * z ∈ PadicInt.powOpenAddSubgroup p m :=
  Ideal.mul_mem_left _ w hz

/-- The evaluation of the bilinear map of a matrix is continuous in the matrix. -/
private lemma continuous_toLinearMap₂_apply (bA : Module.Basis ι ℤ_[p] A)
    (bB : Module.Basis κ ℤ_[p] B) (x : A) (y : B) :
    Continuous fun G : Matrix ι κ ℤ_[p] ↦ Matrix.toLinearMap₂ bA bB G x y := by
  simp only [Matrix.toLinearMap₂_apply]
  exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    continuous_const.mul (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))

/-- In a free module of finite rank over `ℤ_p`, an element divisible by every power of `p` is
zero. -/
private lemma eq_zero_of_forall_pow_dvd [Module.Free ℤ_[p] A] [Module.Finite ℤ_[p] A] {x : A}
    (h : ∀ m : ℕ, ∃ x', x = (p : ℤ_[p]) ^ m • x') : x = 0 := by
  have hI : Ideal.span {(p : ℤ_[p])} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PadicInt.p_nonunit
  have hx : x ∈ (⨅ i : ℕ, (Ideal.span {(p : ℤ_[p])}) ^ i • (⊤ : Submodule ℤ_[p] A)) := by
    rw [Submodule.mem_iInf]
    intro m
    obtain ⟨x', hx'⟩ := h m
    rw [hx', Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul x' ((p : ℤ_[p]) ^ m) (⊤ : Submodule ℤ_[p] A)
      Submodule.mem_top
  rw [Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree _ hI] at hx
  exact (Submodule.mem_bot _).1 hx

/-- **A `p`-adic similitude from finite-level similitudes.** If for every `m` there is a pairing
satisfying the level-`m` conditions `LinearMap.IsLevelSimilitude`, then there is a pairing
`A × B ⟶ ℤ_p` which is an exact `c`-similitude with trivial kernels. -/
theorem exists_isSimilitude_of_forall_level [Module.Free ℤ_[p] A] [Module.Finite ℤ_[p] A]
    [Module.Free ℤ_[p] B] [Module.Finite ℤ_[p] B] (FA : A →ₗ[ℤ_[p]] A) (FB : B →ₗ[ℤ_[p]] B)
    (c : ℤ_[p]) (e : ℕ) (h : ∀ m, ∃ P, IsLevelSimilitude FA FB c e m P) :
    ∃ P : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p], (∀ x y, P (FA x) (FB y) = c * P x y) ∧
      (∀ x, P x = 0 → x = 0) ∧ (∀ y, P.flip y = 0 → y = 0) := by
  classical
  let bA := Module.Free.chooseBasis ℤ_[p] A
  let bB := Module.Free.chooseBasis ℤ_[p] B
  let toB := fun G : Matrix _ _ ℤ_[p] ↦ Matrix.toLinearMap₂ bA bB G
  let S (m : ℕ) : Set (Matrix _ _ ℤ_[p]) := {G | IsLevelSimilitude FA FB c e m (toB G)}
  -- the level conditions are closed
  have hS (m : ℕ) : IsClosed (S m) := by
    have hsim : IsClosed {G : Matrix _ _ ℤ_[p] | ∀ x y, toB G (FA x) (FB y) - c * toB G x y ∈
        PadicInt.powOpenAddSubgroup p m} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ (isClosed_powOpenAddSubgroup m).preimage
        ((continuous_toLinearMap₂_apply bA bB _ _).sub
          (continuous_const.mul (continuous_toLinearMap₂_apply bA bB _ _)))
    have hkerL : IsClosed {G : Matrix _ _ ℤ_[p] | ∀ x, (∀ y, toB G x y ∈
        PadicInt.powOpenAddSubgroup p m) → ∃ x', (p : ℤ_[p]) ^ e • x = (p : ℤ_[p]) ^ m • x'} := by
      have : {G : Matrix _ _ ℤ_[p] | ∀ x, (∀ y, toB G x y ∈ PadicInt.powOpenAddSubgroup p m) →
          ∃ x', (p : ℤ_[p]) ^ e • x = (p : ℤ_[p]) ^ m • x'} =
          ⋂ x, ({G | ∃ j, toB G x (bB j) ∉ PadicInt.powOpenAddSubgroup p m} ∪
            {_G | ∃ x', (p : ℤ_[p]) ^ e • x = (p : ℤ_[p]) ^ m • x'}) := by
        ext G
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
        refine forall_congr' fun x ↦ ⟨fun hx ↦ ?_, fun hx hy ↦ ?_⟩
        · by_cases hj : ∃ j, toB G x (bB j) ∉ PadicInt.powOpenAddSubgroup p m
          · exact Or.inl hj
          · simp only [not_exists, not_not] at hj
            refine Or.inr (hx fun y ↦ ?_)
            rw [← bB.sum_repr y, map_sum]
            exact sum_mem fun j _ ↦ by
              rw [map_smul, smul_eq_mul]
              exact mem_powOpenAddSubgroup_of_mul (hj j) _
        · rcases hx with ⟨j, hj⟩ | hx
          · exact absurd (hy (bB j)) hj
          · exact hx
      rw [this]
      refine isClosed_iInter fun x ↦ IsClosed.union ?_ ?_
      · simp only [Set.ofPred_exists]
        exact isClosed_iUnion_of_finite fun j ↦
          (isOpen_powOpenAddSubgroup m).isClosed_compl.preimage
          (continuous_toLinearMap₂_apply bA bB _ _)
      · by_cases hx : ∃ x', (p : ℤ_[p]) ^ e • x = (p : ℤ_[p]) ^ m • x'
        · simp only [hx, Set.ofPred_true, isClosed_univ]
        · simp only [hx, Set.ofPred_false, isClosed_empty]
    have hkerR : IsClosed {G : Matrix _ _ ℤ_[p] | ∀ y, (∀ x, toB G x y ∈
        PadicInt.powOpenAddSubgroup p m) → ∃ y', (p : ℤ_[p]) ^ e • y = (p : ℤ_[p]) ^ m • y'} := by
      have : {G : Matrix _ _ ℤ_[p] | ∀ y, (∀ x, toB G x y ∈ PadicInt.powOpenAddSubgroup p m) →
          ∃ y', (p : ℤ_[p]) ^ e • y = (p : ℤ_[p]) ^ m • y'} =
          ⋂ y, ({G | ∃ i, toB G (bA i) y ∉ PadicInt.powOpenAddSubgroup p m} ∪
            {_G | ∃ y', (p : ℤ_[p]) ^ e • y = (p : ℤ_[p]) ^ m • y'}) := by
        ext G
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
        refine forall_congr' fun y ↦ ⟨fun hy ↦ ?_, fun hy hx ↦ ?_⟩
        · by_cases hi : ∃ i, toB G (bA i) y ∉ PadicInt.powOpenAddSubgroup p m
          · exact Or.inl hi
          · simp only [not_exists, not_not] at hi
            refine Or.inr (hy fun x ↦ ?_)
            rw [← bA.sum_repr x, map_sum, LinearMap.sum_apply]
            exact sum_mem fun i _ ↦ by
              rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
              exact mem_powOpenAddSubgroup_of_mul (hi i) _
        · rcases hy with ⟨i, hi⟩ | hy
          · exact absurd (hx (bA i)) hi
          · exact hy
      rw [this]
      refine isClosed_iInter fun y ↦ IsClosed.union ?_ ?_
      · simp only [Set.ofPred_exists]
        exact isClosed_iUnion_of_finite fun i ↦
          (isOpen_powOpenAddSubgroup m).isClosed_compl.preimage
          (continuous_toLinearMap₂_apply bA bB _ _)
      · by_cases hy : ∃ y', (p : ℤ_[p]) ^ e • y = (p : ℤ_[p]) ^ m • y'
        · simp only [hy, Set.ofPred_true, isClosed_univ]
        · simp only [hy, Set.ofPred_false, isClosed_empty]
    have h3 := (hsim.inter hkerL).inter hkerR
    convert h3 using 1
    ext G
    simp only [S, IsLevelSimilitude, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  have hmul (m : ℕ) {z : ℤ_[p]} (hz : z ∈ PadicInt.powOpenAddSubgroup p m) :
      (p : ℤ_[p]) * z ∈ PadicInt.powOpenAddSubgroup p (m + 1) := by
    rw [PadicInt.mem_powOpenAddSubgroup, Ideal.mem_span_singleton'] at hz ⊢
    obtain ⟨w, rfl⟩ := hz
    exact ⟨w, by ring⟩
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdec (m : ℕ) : S (m + 1) ⊆ S m := by
    rintro G ⟨hsim, hL, hR⟩
    refine ⟨fun x y ↦ PadicInt.powOpenAddSubgroup_succ_le p m (hsim x y), fun x hx ↦ ?_,
      fun y hy ↦ ?_⟩
    · obtain ⟨x', hx'⟩ := hL ((p : ℤ_[p]) • x) fun y ↦ by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        exact hmul m (hx y)
      refine ⟨x', smul_right_injective A hp0 ?_⟩
      simp only
      rw [smul_comm, hx', smul_smul, pow_succ']
    · obtain ⟨y', hy'⟩ := hR ((p : ℤ_[p]) • y) fun x ↦ by
        rw [map_smul, smul_eq_mul]
        exact hmul m (hy x)
      refine ⟨y', smul_right_injective B hp0 ?_⟩
      simp only
      rw [smul_comm, hy', smul_smul, pow_succ']
  have hne (m : ℕ) : (S m).Nonempty := by
    obtain ⟨P, hP⟩ := h m
    refine ⟨LinearMap.toMatrix₂ bA bB P, ?_⟩
    simp only [S, Set.mem_ofPred_eq, toB, Matrix.toLinearMap₂_toMatrix₂]
    exact hP
  have : CompactSpace (Matrix (Module.Free.ChooseBasisIndex ℤ_[p] A)
      (Module.Free.ChooseBasisIndex ℤ_[p] B) ℤ_[p]) :=
    inferInstanceAs (CompactSpace (_ → _ → ℤ_[p]))
  obtain ⟨G, hG⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne
    (hS 0).isCompact hS
  have hGm (m : ℕ) : G ∈ S m := Set.mem_iInter.1 hG m
  refine ⟨toB G, fun x y ↦ ?_, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · exact sub_eq_zero.1 (PadicInt.eq_zero_of_forall_mem_powOpenAddSubgroup p _
      fun m ↦ (hGm m).1 x y)
  · have hpe : (p : ℤ_[p]) ^ e • x = 0 := eq_zero_of_forall_pow_dvd fun m ↦ by
      obtain ⟨x', hx'⟩ := (hGm m).2.1 x fun y ↦ by
        rw [hx, LinearMap.zero_apply]
        exact zero_mem _
      exact ⟨x', hx'⟩
    exact (smul_eq_zero.1 hpe).resolve_left (pow_ne_zero _ hp0)
  · have hpe : (p : ℤ_[p]) ^ e • y = 0 := eq_zero_of_forall_pow_dvd fun m ↦ by
      obtain ⟨y', hy'⟩ := (hGm m).2.2 y fun x ↦ by
        rw [← LinearMap.flip_apply (toB G), hy, LinearMap.zero_apply]
        exact zero_mem _
      exact ⟨y', hy'⟩
    exact (smul_eq_zero.1 hpe).resolve_left (pow_ne_zero _ hp0)

end LinearMap
