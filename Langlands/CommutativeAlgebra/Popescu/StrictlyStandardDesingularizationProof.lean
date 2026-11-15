import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationStatement
import Langlands.CommutativeAlgebra.Popescu.DesingD

/-! # Proof of Stacks 07F0: desingularization along a strictly standard element -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.Desing

open MvPolynomial

/-- Stacks Lemma 16.7.3 (07F0). -/
theorem strictlyStandardDesingularization : StrictlyStandardDesingularizationStatement.{u} := by
  intro R A Λ _ _ _ _ _ _ _ π hR hΛ f hA C _ _ _ _ _ u v huv
  classical
  -- `Ann(π) = Ann(π⁴) = Ann(π⁸)`
  have hR4 : ∀ x : R, (π ^ 4) ^ 2 * x = 0 → π ^ 4 * x = 0 := by
    intro x hx
    have h1 : π • x = 0 := smul_eq_zero_of_pow_smul_eq_zero (R := R) (M := R) (π := π)
      (fun y hy ↦ hR y hy) 7 (by rw [smul_eq_mul, show 7 + 1 = 4 * 2 from rfl, pow_mul]; exact hx)
    rw [smul_eq_mul] at h1
    calc π ^ 4 * x = π ^ 3 * (π * x) := by ring
      _ = 0 := by rw [h1, mul_zero]
  have hΛ4 : ∀ x : Λ, algebraMap R Λ (π ^ 4) ^ 2 * x = 0 → algebraMap R Λ (π ^ 4) * x = 0 := by
    intro x hx
    have h1 : algebraMap R Λ π • x = 0 :=
      smul_eq_zero_of_pow_smul_eq_zero (R := Λ) (M := Λ) (π := algebraMap R Λ π)
        (fun y hy ↦ hΛ y hy) 7
        (by rw [smul_eq_mul, show 7 + 1 = 4 * 2 from rfl, pow_mul, ← map_pow]; exact hx)
    rw [smul_eq_mul] at h1
    calc algebraMap R Λ (π ^ 4) * x = algebraMap R Λ π ^ 3 * (algebraMap R Λ π * x) := by
          rw [map_pow]; ring
      _ = 0 := by rw [h1, mul_zero]
  -- Stacks 07CP with `ϖ = π⁴`
  obtain ⟨D, _, _, hDfp, ψ, τ, hcompat, hDb, hDc⟩ :=
    exists_lift_D (π ^ 4) (π ^ 8) (by ring) hR4 hΛ4 v
  have hσ : ∀ (a : A) (d : D), (τ.comp u) a = Ideal.Quotient.mk _ d →
      ∃ z, f a - ψ d = algebraMap R Λ (π ^ 4) * z := by
    intro a d had
    refine hcompat (u a) d (f a) had ?_
    rw [← AlgHom.comp_apply, huv]
    rfl
  -- Stacks 07CR and 07CT
  obtain ⟨B, _, _, hBfp, g, j, h, hhg, -, hBπ, hBsm⟩ :=
    exists_desing_lift π hR hΛ hA f ψ (τ.comp u) hσ
  have hDπ : Algebra.Smooth R (Localization.Away (algebraMap R D π)) := by
    apply smooth_away_of_isSmoothAt
    intro q _ hq
    apply hDb q
    rw [map_pow]
    exact fun hmem ↦ hq ((inferInstance : q.IsPrime).mem_of_pow_mem _ hmem)
  have hBsmooth := hBπ hDπ
  refine ⟨B, inferInstance, inferInstance, hBfp, g, h, hhg, hBsmooth, ?_⟩
  -- the comparison of singular loci
  rw [Ideal.map_le_iff_le_comap]
  intro y hy
  obtain ⟨l, hl⟩ := Ideal.Quotient.mk_surjective (v y)
  rw [Ideal.mem_comap, ← hl]
  apply Ideal.mem_map_of_mem
  rw [singularRadical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro 𝔭 ⟨hJ𝔭, h𝔭⟩
  have := h𝔭
  by_contra hl𝔭
  have hπB : algebraMap R B π ∈ singularIdeal R B := by
    rw [singularIdeal, PrimeSpectrum.mem_vanishingIdeal]
    intro x hx
    by_contra hπx
    exact hx ((Algebra.basicOpen_subset_smoothLocus_iff_smooth).mpr hBsmooth hπx)
  have hπ𝔭 : algebraMap R Λ π ∈ 𝔭 := by
    have := hJ𝔭 (Ideal.mem_map_of_mem h hπB)
    rwa [AlgHom.commutes] at this
  have hπ4 : algebraMap R Λ (π ^ 4) ∈ 𝔭 := by
    rw [map_pow]
    exact Ideal.pow_mem_of_mem _ hπ𝔭 _ (by norm_num)
  have hD𝔭 : Algebra.IsSmoothAt R (Ideal.comap ψ 𝔭) := hDc y hy l hl.symm 𝔭 hπ4 hl𝔭
  have hB𝔭 : Algebra.IsSmoothAt R (Ideal.comap h 𝔭) := hBsm 𝔭 hπ𝔭 hD𝔭
  have hnot : ¬ singularIdeal R B ≤ Ideal.comap h 𝔭 := by
    intro hle
    have hclosed : IsClosed (Algebra.smoothLocus R B)ᶜ :=
      (Algebra.isOpen_smoothLocus).isClosed_compl
    have hmem : (⟨Ideal.comap h 𝔭, inferInstance⟩ : PrimeSpectrum B) ∈
        PrimeSpectrum.zeroLocus (singularIdeal R B : Set B) :=
      (PrimeSpectrum.mem_zeroLocus _ _).mpr hle
    rw [singularIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      hclosed.closure_eq] at hmem
    exact hmem hB𝔭
  exact hnot fun b hb ↦ hJ𝔭 (Ideal.mem_map_of_mem h hb)

end Langlands.CommutativeAlgebra.Popescu.Desing
