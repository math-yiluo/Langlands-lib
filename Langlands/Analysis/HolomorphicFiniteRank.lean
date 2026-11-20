import Langlands.Global.EisensteinEvaluationMatrix
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Finite rank in a holomorphic profile family -/

noncomputable section

open Filter Set Matrix Module
open scoped Topology

namespace Langlands.Analysis

variable {X A : Type*}

/-- The point evaluation matrix of a finite family of scalar-valued functions. -/
def profileMatrix {n : ℕ} (p : Fin n → X) (f : Fin n → X → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => f j (p i)

theorem profileMatrix_mulVec {n : ℕ} (p : Fin n → X) (f : Fin n → X → ℂ) (c : Fin n → ℂ) :
    profileMatrix p f *ᵥ c = fun i => Fintype.linearCombination ℂ f c (p i) := by
  ext i
  simp only [profileMatrix, mulVec, dotProduct, Matrix.of_apply, Fintype.linearCombination_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Finite linear independence can be detected by a matrix of point evaluations. -/
theorem exists_profileMatrix_det_ne_zero {n : ℕ} (f : Fin n → X → ℂ)
    (hf : LinearIndependent ℂ f) :
    ∃ p, (profileMatrix p f).det ≠ 0 := by
  have h := Global.EisensteinJet.exists_evaluationEquiv
    (Fintype.linearCombination ℂ f) hf.fintypeLinearCombination_injective
  rw [finrank_fin_fun] at h
  obtain ⟨p, e, he⟩ := h
  refine ⟨p, ?_⟩
  rw [← LinearMap.det_toLin', ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot]
  have hEq : (profileMatrix p f).toLin' = e.toLinearMap := by
    apply LinearMap.ext
    intro v
    funext i
    rw [Matrix.toLin'_apply, profileMatrix_mulVec]
    exact (he v i).symm
  rw [hEq]
  exact e.injective

theorem linearIndependent_of_profileMatrix_det_ne_zero {n : ℕ}
    (p : Fin n → X) (f : Fin n → X → ℂ) (h : (profileMatrix p f).det ≠ 0) :
    LinearIndependent ℂ f := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
  intro c d hcd
  apply Matrix.mulVec_injective_of_det_ne_zero h
  simp only [profileMatrix_mulVec, hcd]

/-- These determinants are holomorphic wherever all point evaluations are holomorphic. -/
theorem analyticOnNhd_profileMatrix_det
    {n : ℕ} (p : Fin n → X) (f : Fin n → ℂ → X → ℂ) {U : Set ℂ}
    (hf : ∀ j x, AnalyticOnNhd ℂ (fun t => f j t x) U) :
    AnalyticOnNhd ℂ (fun t => (profileMatrix p (fun j => f j t)).det) U := by
  intro z hz
  simp_rw [Matrix.det_apply', profileMatrix, Matrix.of_apply]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun j _ => hf j (p (σ j)) z hz)

private theorem dense_ne_zero_on_open {U W : Set ℂ} (hU : IsPreconnected U)
    (hW : IsOpen W) (hWU : W ⊆ U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hn : ∃ t ∈ U, f t ≠ 0) :
    Dense {z : W | f z.val ≠ 0} := by
  rw [dense_iff_inter_open]
  intro O hO hne
  by_contra hnO
  obtain ⟨o, ho⟩ := hne
  obtain ⟨t, ht, hft⟩ := hn
  have hS := hW.isOpenEmbedding_subtypeVal.isOpenMap O hO
  have heq : f =ᶠ[𝓝 o.val] 0 := by
    filter_upwards [hS.mem_nhds (mem_image_of_mem Subtype.val ho)] with w hw
    obtain ⟨v, hv, rfl⟩ := hw
    change f v.val = 0
    by_contra hv'
    exact hnO ⟨v, hv, hv'⟩
  exact hft (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU (hWU o.property) heq ht)

/-- Pointwise finite rank on a nonempty open regular subset bounds the rank
uniformly on the connected holomorphy domain. -/
theorem exists_uniformProfileRankBound (f : A → ℂ → X → ℂ) {U W : Set ℂ}
    (hU : IsPreconnected U) (hW : IsOpen W) (hWU : W ⊆ U) (hne : W.Nonempty)
    (hf : ∀ a x, AnalyticOnNhd ℂ (fun t => f a t x) U)
    (hfin : ∀ t ∈ W, FiniteDimensional ℂ (Submodule.span ℂ (range fun a => f a t))) :
    ∃ n : ℕ, ∀ t ∈ U, ∀ s : Fin (n + 1) → A, ¬ LinearIndependent ℂ (fun j => f (s j) t) := by
  classical
  by_contra! hn
  choose t ht s hs using hn
  choose p hp using fun n : ℕ => exists_profileMatrix_det_ne_zero _ (hs n)
  let Δ (n : ℕ) (z : ℂ) := (profileMatrix (p n) (fun j => f (s n j) z)).det
  have hΔ (n : ℕ) : AnalyticOnNhd ℂ (Δ n) U :=
    analyticOnNhd_profileMatrix_det _ _ (fun j => hf (s n j))
  let V (n : ℕ) : Set W := {z | Δ n z.val ≠ 0}
  have hopen (n : ℕ) : IsOpen (V n) := by
    have hc : Continuous (fun z : W => Δ n z.val) :=
      ((hΔ n).continuousOn.mono hWU).domRestrict
    exact isClosed_singleton.isOpen_compl.preimage hc
  have hdense (n : ℕ) : Dense (V n) :=
    dense_ne_zero_on_open hU hW hWU (hΔ n) ⟨t n, ht n, hp n⟩
  let : BaireSpace W := hW.baireSpace
  let : Nonempty W := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨z, hz⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  let S := Submodule.span ℂ (range fun a => f a z.val)
  let : FiniteDimensional ℂ S := hfin z.val z.property
  let n := finrank ℂ S
  have hi := linearIndependent_of_profileMatrix_det_ne_zero (p n) _ (mem_iInter.mp hz n)
  let v (j : Fin (n + 1)) : S := ⟨f (s n j) z.val, Submodule.subset_span (mem_range_self _)⟩
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hi
  have hcard := hv.fintype_card_le_finrank
  exact Nat.not_succ_le_self n (by simpa only [Fintype.card_fin] using hcard)

/-- Some fixed finite family spans every profile at each regular parameter for
one of its nonzero evaluation minors. -/
theorem exists_spanningProfileMatrix (f : A → ℂ → X → ℂ) {U W : Set ℂ}
    (hU : IsPreconnected U) (hW : IsOpen W) (hWU : W ⊆ U) (hne : W.Nonempty)
    (hf : ∀ a x, AnalyticOnNhd ℂ (fun t => f a t x) U)
    (hfin : ∀ t ∈ W, FiniteDimensional ℂ (Submodule.span ℂ (range fun a => f a t))) :
    ∃ (n : ℕ) (s : Fin n → A) (p : Fin n → X) (t₁ : ℂ), t₁ ∈ U ∧
      (profileMatrix p (fun j => f (s j) t₁)).det ≠ 0 ∧
      ∀ t ∈ U, (profileMatrix p (fun j => f (s j) t)).det ≠ 0 →
        ∀ a, f a t ∈ Submodule.span ℂ (range fun j => f (s j) t) := by
  classical
  obtain ⟨N, hN⟩ := exists_uniformProfileRankBound f hU hW hWU hne hf hfin
  let P (n : ℕ) := ∃ t ∈ U, ∃ s : Fin n → A, LinearIndependent ℂ (fun j => f (s j) t)
  let n := Nat.findGreatest P N
  have hn : n ≤ N := Nat.findGreatest_le _
  have hp₀ : P 0 :=
    ⟨hne.choose, hWU hne.choose_spec, Fin.elim0, linearIndependent_empty_type⟩
  have hp : P n := Nat.findGreatest_spec (Nat.zero_le N) hp₀
  have hnmax : ¬ P (n + 1) := by
    intro h
    by_cases hle : n + 1 ≤ N
    · exact Nat.not_succ_le_self n (Nat.le_findGreatest hle h)
    · have heq : n = N := by omega
      obtain ⟨t, ht, s, hs⟩ := heq ▸ h
      exact hN t ht s hs
  obtain ⟨t₁, ht₁, s, hs⟩ := hp
  obtain ⟨p, hp⟩ := exists_profileMatrix_det_ne_zero _ hs
  refine ⟨n, s, p, t₁, ht₁, hp, fun t ht hd a => ?_⟩
  by_contra ha
  have hi := linearIndependent_of_profileMatrix_det_ne_zero p _ hd
  apply hnmax
  refine ⟨t, ht, Fin.cons a s, ?_⟩
  change LinearIndependent ℂ ((fun a => f a t) ∘ Fin.cons a s)
  rw [Fin.comp_cons]
  have h := hi.finCons ha
  exact h

end Langlands.Analysis
