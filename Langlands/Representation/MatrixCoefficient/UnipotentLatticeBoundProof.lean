import Langlands.Representation.MatrixCoefficient.UnipotentLatticeBoundStatement
import Langlands.Representation.MatrixCoefficient.IntegerLatticeProof
import Langlands.LinearAlgebra.UnipotentBinomialProof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Uniform-degree growth of unipotent lattice coefficients -/

namespace Langlands.UnipotentLatticeBound

open Polynomial
open IntegerLatticeExponentialPolynomial

/-- A scalar polynomial of degree at most `D` admits a bound of degree `D`. -/
theorem exists_polynomial_bound (p : ℂ[X]) (D : ℕ) (hD : p.natDegree ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖p.eval z‖ ≤ C * (1 + ‖z‖) ^ D := by
  refine ⟨∑ j ∈ Finset.range (D + 1), ‖p.coeff j‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun z => ?_⟩
  rw [p.eval_eq_sum_range' (Nat.lt_succ_of_le hD)]
  calc
    ‖∑ j ∈ Finset.range (D + 1), p.coeff j * z ^ j‖ ≤
        ∑ j ∈ Finset.range (D + 1), ‖p.coeff j * z ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (D + 1), ‖p.coeff j‖ * (1 + ‖z‖) ^ D := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ (norm_nonneg z) (by linarith : ‖z‖ ≤ 1 + ‖z‖) j).trans
        (pow_le_pow_right₀ (by have := norm_nonneg z; linarith)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = _ := (Finset.sum_mul ..).symm

/-- A binomial coefficient of order below `r` has growth bounded with degree `r`. -/
theorem exists_binomial_bound (r j : ℕ) (hj : j ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      ‖Ring.choose (n : ℂ) j‖ ≤ C * (1 + |(n : ℝ)|) ^ r := by
  obtain ⟨C, hC, h⟩ := exists_polynomial_bound
    ((j.factorial : ℂ)⁻¹ • descPochhammer ℂ j) r
    ((natDegree_smul_le ..).trans ((descPochhammer_natDegree ℂ j).le.trans hj))
  exact ⟨C, hC, fun n => by
    have hn := h (n : ℂ)
    rw [complexBinomialCoefficientPolynomial j (n : ℂ), Complex.norm_intCast] at hn
    exact hn⟩

universe u

/-- Polynomial growth with degree determined before the vector and functional. -/
theorem coefficient_bound : UnipotentLatticeCoefficientBoundStatement.{u} := by
  intro d r
  induction d with
  | zero =>
    intro V _ _ ρ hρ v ell
    refine ⟨‖ell v‖, norm_nonneg _, fun n => ?_⟩
    rw [Subsingleton.elim (Multiplicative.ofAdd n) 1]
    simp [matrixCoefficient]
  | succ d ih =>
    intro V _ _ ρ hρ v ell
    let ρ' : Representation ℂ (Multiplicative (Fin d → ℤ)) V := ρ.comp (consZero d)
    let T : (Module.End ℂ V)ˣ :=
      ρ.asGroupHom (Multiplicative.ofAdd (Pi.single 0 1 : Fin (d + 1) → ℤ))
    let N : Module.End ℂ V := (T : Module.End ℂ V) - 1
    have hN : N ^ r = 0 := by
      simpa only [N, T, Representation.asGroupHom_apply] using hρ 0
    have hρ' (i : Fin d) :
        (ρ' (Multiplicative.ofAdd (Pi.single i 1)) - 1) ^ r = 0 := by
      have hsingle : consZero d (Multiplicative.ofAdd (Pi.single i 1)) =
          Multiplicative.ofAdd (Pi.single i.succ 1) := by
        apply Multiplicative.toAdd.injective
        ext j
        refine Fin.cases ?_ (fun k => ?_) j <;> simp [consZero, Pi.single_apply]
      simpa only [ρ', MonoidHom.comp_apply, hsingle] using hρ i.succ
    choose C hC hbound using fun j : Fin r => ih V ρ' hρ' ((N ^ (j : ℕ)) v) ell
    choose A hA hchoose using fun j : Fin r =>
      exists_binomial_bound r j (Nat.le_of_lt j.isLt)
    refine ⟨∑ j : Fin r, A j * C j,
      Finset.sum_nonneg (fun j _ => mul_nonneg (hA j) (hC j)), fun n => ?_⟩
    have hdecomp : ρ (Multiplicative.ofAdd n) v =
        ρ' (Multiplicative.ofAdd (Fin.tail n))
          (((T ^ (n 0) : (Module.End ℂ V)ˣ) : Module.End ℂ V) v) := by
      simp only [ρ', T, MonoidHom.coe_comp, Function.comp_apply, ← map_zpow,
        Representation.asGroupHom_apply, ← Module.End.mul_apply, ← map_mul,
        ← ofAdd_eq_consZero_mul]
    have hexpand : matrixCoefficient ρ ell v (Multiplicative.ofAdd n) =
        ∑ j : Fin r, Ring.choose (n 0 : ℂ) j *
          matrixCoefficient ρ' ell ((N ^ (j : ℕ)) v)
            (Multiplicative.ofAdd (Fin.tail n)) := by
      change ell (ρ (Multiplicative.ofAdd n) v) = _
      rw [hdecomp, integerUnipotentBinomial V T r hN]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
        smul_eq_mul, matrixCoefficient, ← Fin.sum_univ_eq_sum_range]
      rfl
    let B : ℝ := 1 + ∑ i, |(n i : ℝ)|
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hhead : 1 + |(n 0 : ℝ)| ≤ B := by
      dsimp [B]
      rw [Fin.sum_univ_succ]
      have : 0 ≤ ∑ i : Fin d, |(n i.succ : ℝ)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith
    have htail : 1 + ∑ i, |(Fin.tail n i : ℝ)| ≤ B := by
      dsimp [B]
      rw [Fin.sum_univ_succ]
      change 1 + ∑ i : Fin d, |(n i.succ : ℝ)| ≤
        1 + (|(n 0 : ℝ)| + ∑ i : Fin d, |(n i.succ : ℝ)|)
      linarith [abs_nonneg (n 0 : ℝ)]
    rw [hexpand]
    calc
      ‖∑ j : Fin r, Ring.choose (n 0 : ℂ) j *
          matrixCoefficient ρ' ell ((N ^ (j : ℕ)) v)
            (Multiplicative.ofAdd (Fin.tail n))‖ ≤
          ∑ j : Fin r, ‖Ring.choose (n 0 : ℂ) j *
            matrixCoefficient ρ' ell ((N ^ (j : ℕ)) v)
              (Multiplicative.ofAdd (Fin.tail n))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin r, (A j * C j) * B ^ ((d + 1) * r) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        have h₁ : ‖Ring.choose (n 0 : ℂ) j‖ ≤ A j * B ^ r :=
          (hchoose j (n 0)).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hhead r) (hA j))
        have h₂ : ‖matrixCoefficient ρ' ell ((N ^ (j : ℕ)) v)
            (Multiplicative.ofAdd (Fin.tail n))‖ ≤ C j * B ^ (d * r) :=
          (hbound j (Fin.tail n)).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) htail (d * r)) (hC j))
        calc
          _ ≤ (A j * B ^ r) * (C j * B ^ (d * r)) :=
            mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg (hA j) (pow_nonneg hB _))
          _ = (A j * C j) * B ^ ((d + 1) * r) := by
            rw [mul_mul_mul_comm, ← pow_add]
            congr 2
            ring
      _ = _ := (Finset.sum_mul ..).symm

end Langlands.UnipotentLatticeBound

namespace Langlands

/-- Uniform-degree polynomial coefficient bound for globally unipotent lattice actions. -/
theorem unipotentLatticeCoefficientBound : UnipotentLatticeCoefficientBoundStatement.{u} :=
  UnipotentLatticeBound.coefficient_bound

end Langlands
