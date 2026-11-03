import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Langlands.CommutativeAlgebra.LocallySplit.Basic

/-! # Dominated factorizations

For a tuple `x : ι → M` and coefficients `A : ι → κ → R`, `Dominates x A` says that every
vanishing tensor `∑ i, x i ⊗ ν i = 0` forces `∑ i, A i k • ν i = 0` for all `k`.
`HasDominatedFactorizations R M` says that every finite tuple of `M` factors as
`x i = ∑ k, A i k • y k` through a finite free module with `A` dominating `x`.

Main results:
* `LocallySplit.hasDominatedFactorizations`: locally split modules have dominated
  factorizations;
* `hasDominatedFactorizations_of_baseChange`: for a flat module `M` and a faithfully flat
  algebra `R'`, dominated factorizations descend from `R' ⊗[R] M` to `M`. -/

universe w u u' v

open TensorProduct

namespace Langlands.CommutativeAlgebra

section Defs

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The coefficients `A` dominate the tuple `x`: whenever `∑ i, x i ⊗ ν i = 0` in `M ⊗ N`
(for an `R`-module `N` in universe `w`), we have `∑ i, A i k • ν i = 0` for every `k`. -/
def Dominates {ι κ : Type} [Fintype ι] (x : ι → M) (A : ι → κ → R) : Prop :=
  ∀ (N : Type w) [AddCommGroup N] [Module R N] (ν : ι → N),
    ∑ i, x i ⊗ₜ[R] ν i = 0 → ∀ k, ∑ i, A i k • ν i = 0

variable (R M) in
/-- Every finite tuple `x` of `M` factors as `x i = ∑ k, A i k • y k` through a finite free
module, with coefficients `A` dominating `x` (tested against modules in universe `w`). -/
def HasDominatedFactorizations : Prop :=
  ∀ (n : ℕ) (x : Fin n → M), ∃ (m : ℕ) (A : Fin n → Fin m → R) (y : Fin m → M),
    (∀ i, x i = ∑ k, A i k • y k) ∧ Dominates.{w} x A

end Defs

section LocallySplit

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A locally split module has dominated factorizations: take the coefficients `φ (x i)`. -/
theorem LocallySplit.hasDominatedFactorizations (h : LocallySplit R M) :
    HasDominatedFactorizations.{w} R M := by
  intro n x
  obtain ⟨r, φ, y, hy⟩ := h n x
  refine ⟨r, fun i j => φ (x i) j, y, fun i => (hy i).symm, ?_⟩
  intro N _ _ ν hν j
  have := congrArg
    (fun t => TensorProduct.lid R N (LinearMap.rTensor N ((LinearMap.proj j).comp φ) t)) hν
  simpa [map_sum] using this

end LocallySplit

section Descent

variable {R : Type u} [CommRing R] {R' : Type u'} [CommRing R'] [Algebra R R']
  {M : Type v} [AddCommGroup M] [Module R M]

/-- Every element of `R' ⊗[R] M` is an `R'`-linear combination of finitely many `1 ⊗ₜ m`. -/
theorem exists_eq_sum_smul_one_tmul (t : R' ⊗[R] M) :
    ∃ (p : ℕ) (c : Fin p → R') (z : Fin p → M), t = ∑ j, c j • ((1 : R') ⊗ₜ[R] z j) := by
  induction t with
  | tmul r m => exact ⟨1, fun _ => r, fun _ => m, by simp [TensorProduct.smul_tmul']⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨p₁, c₁, z₁, rfl⟩ := h₁
    obtain ⟨p₂, c₂, z₂, rfl⟩ := h₂
    exact ⟨p₁ + p₂, Fin.append c₁ c₂, Fin.append z₁ z₂, by simp [Fin.sum_univ_add]⟩

variable [Module.FaithfullyFlat R R'] [Module.Flat R M]

/-- The descent step. Suppose that after base change the tuple `1 ⊗ x` is an `R'`-linear
combination `1 ⊗ x i = ∑ l, B i l • (1 ⊗ z l)` of base-changed elements of `M`, and that every
vanishing tensor `∑ i, x i ⊗ ν i = 0` forces `∑ i, B i l • (1 ⊗ ν i) = 0` in `R' ⊗[R] N`.
Then `x` has a dominated factorization over `R`. -/
theorem exists_dominated_factorization_of_baseChange {n : ℕ} (x : Fin n → M) {κ : Type}
    [Fintype κ] (z : κ → M) (B : Fin n → κ → R')
    (hxz : ∀ i, (1 : R') ⊗ₜ[R] x i = ∑ l, B i l • ((1 : R') ⊗ₜ[R] z l))
    (hB : ∀ (N : Type w) [AddCommGroup N] [Module R N] (ν : Fin n → N),
      ∑ i, x i ⊗ₜ[R] ν i = 0 → ∀ l, ∑ i, B i l • ((1 : R') ⊗ₜ[R] ν i) = 0) :
    ∃ (m : ℕ) (A : Fin n → Fin m → R) (y : Fin m → M),
      (∀ i, x i = ∑ k, A i k • y k) ∧ Dominates.{w} x A := by
  classical
  -- For each `i`, the relation `x i ⊗ 1 - ∑ l, z l ⊗ B i l = 0` in `M ⊗[R] R'` vanishes
  -- trivially, because `R'` is flat.
  have hvan : ∀ i, VanishesTrivially R (fun o : Option κ => o.elim (x i) z)
      (fun o : Option κ => o.elim (1 : R') fun l => -B i l) := by
    intro i
    apply TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective
    · exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    · have h1 : (1 : R') ⊗ₜ[R] x i = ∑ l, B i l ⊗ₜ[R] z l := by
        rw [hxz i]; simp [TensorProduct.smul_tmul']
      have h2 := congrArg (TensorProduct.comm R R' M) h1
      simp only [TensorProduct.comm_tmul, map_sum] at h2
      simp [Fintype.sum_option, h2, TensorProduct.tmul_neg]
  choose k a y' hya hay using hvan
  beta_reduce at hya hay
  -- Collect all these relations into one map `f : R^K → R^(n ⊕ κ)` killed by `X`.
  let e : Fin n → Option κ → (Fin n ⊕ κ → R) := fun i o =>
    Pi.single (o.elim (Sum.inl i) Sum.inr) 1
  let v : (Σ i, Fin (k i)) → (Fin n ⊕ κ → R) := fun q => ∑ o, a q.1 o q.2 • e q.1 o
  let X : (Fin n ⊕ κ → R) →ₗ[R] M := Fintype.linearCombination R (Sum.elim x z)
  have hXe : ∀ i o, X (e i o) = o.elim (x i) z := by
    intro i o
    cases o <;> simp [X, e]
  have hXv : ∀ q, X (v q) = 0 := by
    intro q
    simpa [v, map_sum, hXe] using hay q.1 q.2
  have hXf : X ∘ₗ Fintype.linearCombination R v = 0 := by
    ext g
    simp [Fintype.linearCombination_apply, hXv]
  obtain ⟨m, a₀, y₀, hX, ha₀⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hXf
  have hy₀ : ∀ g : Fin m →₀ R, y₀ g = ∑ k, g k • y₀ (Finsupp.single k 1) := by
    intro g
    calc y₀ g = y₀ (∑ k, Finsupp.single k (g k)) := by rw [Finsupp.univ_sum_single]
      _ = _ := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← map_smul, Finsupp.smul_single_one]
  refine ⟨m, fun i k => a₀ (e i none) k, fun k => y₀ (Finsupp.single k 1), fun i => ?_, ?_⟩
  · have := LinearMap.congr_fun hX (e i none)
    rw [hXe, LinearMap.comp_apply, hy₀] at this
    exact this
  · -- The key identity `algebraMap (A i k) = ∑ l, B i l * algebraMap (C l k)` in `R'`.
    have hrel : ∀ i j (c : Fin m), ∑ o, a i o j * a₀ (e i o) c = 0 := by
      intro i j c
      have := LinearMap.congr_fun ha₀ (Pi.single ⟨i, j⟩ 1)
      simpa [v, map_sum] using congrArg (fun g : Fin m →₀ R => g c) this
    have hkey : ∀ i (c : Fin m), algebraMap R R' (a₀ (e i none) c) =
        ∑ l, B i l * algebraMap R R' (a₀ (Pi.single (Sum.inr l) 1) c) := by
      intro i c
      have h : ∑ o, (o.elim (1 : R') fun l => -B i l) * algebraMap R R' (a₀ (e i o) c) = 0 := by
        calc _ = ∑ o, ∑ j, (a i o j • y' i j) * algebraMap R R' (a₀ (e i o) c) := by
                refine Finset.sum_congr rfl fun o _ => ?_
                rw [hya i o, Finset.sum_mul]
          _ = ∑ j, y' i j * algebraMap R R' (∑ o, a i o j * a₀ (e i o) c) := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ => ?_
                simp only [map_sum, map_mul, Finset.mul_sum, Algebra.smul_def]
                refine Finset.sum_congr rfl fun o _ => ?_
                ring
          _ = 0 := by simp [hrel]
      simp only [Fintype.sum_option, Option.elim, one_mul, neg_mul, Finset.sum_neg_distrib] at h
      exact (add_neg_eq_zero.mp h)
    intro N _ _ ν hν c
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := R') N
    have h0 : ∀ i, (1 : R') ⊗ₜ[R] (a₀ (e i none) c • ν i) =
        ∑ l, algebraMap R R' (a₀ (Pi.single (Sum.inr l) 1) c) •
          (B i l • ((1 : R') ⊗ₜ[R] ν i)) := by
      intro i
      rw [TensorProduct.tmul_smul, ← algebraMap_smul R', hkey, Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_comm]
    simp only [TensorProduct.mk_apply, TensorProduct.tmul_sum, h0, map_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← Finset.smul_sum, hB N ν hν l, smul_zero]

/-- Dominated factorizations descend along a faithfully flat ring map, for flat modules. -/
theorem hasDominatedFactorizations_of_baseChange
    (h : HasDominatedFactorizations.{max u' w} R' (R' ⊗[R] M)) :
    HasDominatedFactorizations.{w} R M := by
  intro n x
  obtain ⟨m, A', y', hxy, hdom⟩ := h n (fun i => (1 : R') ⊗ₜ[R] x i)
  choose p c z hz using fun k => exists_eq_sum_smul_one_tmul (R := R) (y' k)
  refine exists_dominated_factorization_of_baseChange x (κ := Σ k, Fin (p k))
    (fun q => z q.1 q.2) (fun i q => A' i q.1 * c q.1 q.2) (fun i => ?_) ?_
  · rw [hxy i, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hz k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul]
  · intro N _ _ ν hν q
    have h0 : ∑ i, ((1 : R') ⊗ₜ[R] x i) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] ν i) = 0 := by
      have := congrArg (AlgebraTensorModule.distribBaseChange R R' M N)
        (congrArg (fun t => (1 : R') ⊗ₜ[R] t) hν)
      simpa [TensorProduct.tmul_sum, map_sum] using this
    have := hdom (R' ⊗[R] N) (fun i => (1 : R') ⊗ₜ[R] ν i) h0 q.1
    simp only [mul_comm (A' _ _), mul_smul, ← Finset.smul_sum, this, smul_zero]

end Descent

end Langlands.CommutativeAlgebra
