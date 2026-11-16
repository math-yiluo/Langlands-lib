import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealBlockJacquetFunctional

/-!
# Block Fourier modes and integrals over `O(N)`

For continuous right `O(N)`-finite functions `φ, ψ` on `GL_N(ℝ)` and a block `p` this module
expresses `∫_{O(N)} φ ψ` through the block Fourier coefficients (a Parseval formula), and deduces
the transposition rule for block multipliers and the orthogonality of complementary sets of
block modes.
-/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealBlockTransposition

open RealPrincipalSeriesDuality RealBlockFourierFinite RealBlockJacquet

attribute [local instance] measurableSpaceK

local instance borelSpaceK' (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {N p : ℕ}

/-- The rotation `r_p(θ)` as an element of `O(N)`. -/
def rotK (N p : ℕ) (θ : ℝ) : unitaryCompact ℝ N :=
  ⟨blockRotation N p θ, blockRotation_mem_unitaryCompact N p θ⟩

theorem two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- **Product expansion.** For continuous right `O(N)`-finite `φ, ψ` there is a bound `D` such
that for every `D' ≥ D`, `g ∈ O(N)` and `θ`,
`φ(r_p(θ) g) ψ(r_p(θ) g) = (2π)⁻² Σ_{i,j ∈ [-D', D']} Φ_i φ(g) Φ_j ψ(g) e^{i(i+j)θ}`. -/
theorem exists_mul_eq_sum (hp : p + 1 < N)
    {φ ψ : Langlands.GeneralLinear N ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφK : φ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (hψK : ψ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) :
    ∃ D : ℕ, ∀ D' : ℕ, D ≤ D' → ∀ g ∈ unitaryCompact ℝ N, ∀ θ : ℝ,
      φ (blockRotation N p θ * g) * ψ (blockRotation N p θ * g) =
        (2 * (Real.pi : ℂ))⁻¹ * (2 * (Real.pi : ℂ))⁻¹ *
          ∑ i ∈ Finset.Icc (-(D' : ℤ)) D', ∑ j ∈ Finset.Icc (-(D' : ℤ)) D',
            blockFourierCoefficient N p i φ g * blockFourierCoefficient N p j ψ g *
              expMode (i + j) θ := by
  obtain ⟨D₁, hD₁⟩ := exists_trigPoly_of_mem_kFiniteVectors hp hφ hφK
  obtain ⟨D₂, hD₂⟩ := exists_trigPoly_of_mem_kFiniteVectors hp hψ hψK
  refine ⟨max D₁ D₂, fun D' hD' g hg θ => ?_⟩
  have h₁ := eq_sum_coeff_of_mem_trigPoly
    (trigPoly_mono (le_trans (le_max_left _ _) hD') (hD₁ g hg)) θ
  have h₂ := eq_sum_coeff_of_mem_trigPoly
    (trigPoly_mono (le_trans (le_max_right _ _) hD') (hD₂ g hg)) θ
  simp only [← blockFourierCoefficient_eq_coeff] at h₁ h₂
  rw [h₁, h₂, mul_mul_mul_comm, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← congrFun (expMode_add i j) θ, Pi.mul_apply]
  ring

/-- **Parseval formula along a block.** For continuous right `O(N)`-finite `φ, ψ` there is a
bound `D` such that for every `D' ≥ D`,
`∫_{O(N)} φ ψ = (2π)⁻² Σ_{j ∈ [-D', D']} ∫_{O(N)} Φ_j φ · Φ_{-j} ψ`. -/
theorem exists_integral_mul_eq_sum (hp : p + 1 < N)
    {φ ψ : Langlands.GeneralLinear N ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφK : φ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (hψK : ψ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) :
    ∃ D : ℕ, ∀ D' : ℕ, D ≤ D' →
      ∫ k, φ (k : Langlands.GeneralLinear N ℝ) * ψ (k : Langlands.GeneralLinear N ℝ) ∂haarK N =
        (2 * (Real.pi : ℂ))⁻¹ * (2 * (Real.pi : ℂ))⁻¹ *
          ∑ j ∈ Finset.Icc (-(D' : ℤ)) D',
            ∫ k, blockFourierCoefficient N p j φ (k : Langlands.GeneralLinear N ℝ) *
              blockFourierCoefficient N p (-j) ψ (k : Langlands.GeneralLinear N ℝ) ∂haarK N := by
  obtain ⟨D, hD⟩ := exists_mul_eq_sum hp hφ hψ hφK hψK
  refine ⟨D, fun D' hD' => ?_⟩
  set I := Finset.Icc (-(D' : ℤ)) D' with hI
  set c : ℂ := (2 * (Real.pi : ℂ))⁻¹ with hc
  set C : ℂ := ∫ k, φ (k : Langlands.GeneralLinear N ℝ) * ψ (k : Langlands.GeneralLinear N ℝ)
    ∂haarK N with hC
  set A : ℤ → ℤ → ℂ := fun i j =>
    ∫ k, blockFourierCoefficient N p i φ (k : Langlands.GeneralLinear N ℝ) *
      blockFourierCoefficient N p j ψ (k : Langlands.GeneralLinear N ℝ) ∂haarK N with hA
  have hcont : ∀ i j : ℤ, Continuous fun k : unitaryCompact ℝ N =>
      blockFourierCoefficient N p i φ (k : Langlands.GeneralLinear N ℝ) *
        blockFourierCoefficient N p j ψ (k : Langlands.GeneralLinear N ℝ) := fun i j =>
    (continuous_comp_val (continuous_blockFourierCoefficient p i hφ)).mul
      (continuous_comp_val (continuous_blockFourierCoefficient p j hψ))
  -- the integral over `O(N)` as a trigonometric polynomial in `θ`
  have key : ∀ θ : ℝ, C = c * c * ∑ i ∈ I, ∑ j ∈ I, A i j * expMode (i + j) θ := by
    intro θ
    rw [hC, ← integral_mul_left_eq_self _ (rotK N p θ)]
    have e : ∀ k : unitaryCompact ℝ N,
        φ ((rotK N p θ * k : unitaryCompact ℝ N) : Langlands.GeneralLinear N ℝ) *
          ψ ((rotK N p θ * k : unitaryCompact ℝ N) : Langlands.GeneralLinear N ℝ) =
        c * c * ∑ i ∈ I, ∑ j ∈ I,
          blockFourierCoefficient N p i φ (k : Langlands.GeneralLinear N ℝ) *
            blockFourierCoefficient N p j ψ (k : Langlands.GeneralLinear N ℝ) *
              expMode (i + j) θ := fun k =>
      hD D' hD' (k : Langlands.GeneralLinear N ℝ) k.2 θ
    simp_rw [e]
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_mul_const]
      · exact fun j _ => integrable_of_continuous ((hcont i j).mul continuous_const)
    · exact fun i _ => integrable_of_continuous
        (continuous_finsetSum _ fun j _ => (hcont i j).mul continuous_const)
  -- integrate over `θ ∈ [0, 2π]`
  have hint : (∫ θ in (0 : ℝ)..2 * Real.pi, C) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, c * c * ∑ i ∈ I, ∑ j ∈ I, A i j * expMode (i + j) θ :=
    intervalIntegral.integral_congr fun θ _ => key θ
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum] at hint
  · have hsum : ∀ i ∈ I, (∫ θ in (0 : ℝ)..2 * Real.pi, ∑ j ∈ I, A i j * expMode (i + j) θ) =
        A i (-i) * (2 * (Real.pi : ℂ)) := by
      intro i hi
      rw [intervalIntegral.integral_finsetSum]
      · rw [Finset.sum_eq_single_of_mem (-i)]
        · rw [intervalIntegral.integral_const_mul]
          unfold expMode
          rw [integral_exp_int_mul]
          simp
        · rw [hI, Finset.mem_Icc] at hi ⊢
          omega
        · intro j _ hj
          rw [intervalIntegral.integral_const_mul]
          unfold expMode
          rw [integral_exp_int_mul]
          simp [show i + j ≠ 0 by omega]
      · exact fun j _ => ((continuous_expMode (i + j)).const_smul (A i j)).intervalIntegrable _ _
    rw [Finset.sum_congr rfl hsum, ← Finset.sum_mul] at hint
    have h2 : ((2 * Real.pi - 0 : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; ring
    rw [Complex.real_smul, h2] at hint
    have := mul_right_cancel₀ two_pi_ne_zero
      (show C * (2 * (Real.pi : ℂ)) = (c * c * ∑ i ∈ I, A i (-i)) * (2 * (Real.pi : ℂ)) by
        rw [mul_comm C, hint]; ring)
    exact this
  · exact fun i _ => (continuous_finsetSum _ fun j _ =>
      (continuous_expMode (i + j)).const_smul (A i j)).intervalIntegrable _ _

/-- **Transposition of block multipliers.** Let `φ, φ', ψ, ψ'` be continuous right
`O(N)`-finite functions and `μ : ℤ → ℂ`, with `Φ_j φ' = μ(j) Φ_j φ` and
`Φ_j ψ' = μ(-j) Φ_j ψ` on `O(N)` for all `j`. Then `∫_{O(N)} φ' ψ = ∫_{O(N)} φ ψ'`. -/
theorem integral_mul_eq_of_multiplier (hp : p + 1 < N)
    {φ φ' ψ ψ' : Langlands.GeneralLinear N ℝ → ℂ}
    (hφ : Continuous φ) (hφ' : Continuous φ') (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hφK : φ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (hφK' : φ' ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (hψK : ψ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (hψK' : ψ' ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (μ : ℤ → ℂ)
    (hφμ : ∀ j : ℤ, ∀ g ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j φ' g = μ j * blockFourierCoefficient N p j φ g)
    (hψμ : ∀ j : ℤ, ∀ g ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j ψ' g = μ (-j) * blockFourierCoefficient N p j ψ g) :
    ∫ k, φ' (k : Langlands.GeneralLinear N ℝ) * ψ (k : Langlands.GeneralLinear N ℝ) ∂haarK N =
      ∫ k, φ (k : Langlands.GeneralLinear N ℝ) * ψ' (k : Langlands.GeneralLinear N ℝ) ∂haarK N := by
  obtain ⟨D₁, hD₁⟩ := exists_integral_mul_eq_sum hp hφ' hψ hφK' hψK
  obtain ⟨D₂, hD₂⟩ := exists_integral_mul_eq_sum hp hφ hψ' hφK hψK'
  rw [hD₁ (max D₁ D₂) (le_max_left _ _), hD₂ (max D₁ D₂) (le_max_right _ _)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [hφμ j _ k.2, hψμ (-j) _ k.2, neg_neg]
  ring

/-- **Orthogonality of complementary block modes.** If `Φ_j φ = 0` on `O(N)` for `|j| < l` and
`Φ_j ψ = 0` on `O(N)` for `|j| ≥ l`, then `∫_{O(N)} φ ψ = 0`. -/
theorem integral_mul_eq_zero_of_modes (hp : p + 1 < N)
    {φ ψ : Langlands.GeneralLinear N ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφK : φ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (hψK : ψ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) (l : ℕ)
    (hφl : ∀ j : ℤ, |j| < l → ∀ g ∈ unitaryCompact ℝ N, blockFourierCoefficient N p j φ g = 0)
    (hψl : ∀ j : ℤ, (l : ℤ) ≤ |j| → ∀ g ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j ψ g = 0) :
    ∫ k, φ (k : Langlands.GeneralLinear N ℝ) * ψ (k : Langlands.GeneralLinear N ℝ) ∂haarK N =
      0 := by
  obtain ⟨D, hD⟩ := exists_integral_mul_eq_sum hp hφ hψ hφK hψK
  rw [hD D le_rfl]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
  refine (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)).trans (integral_zero _ _)
  rcases lt_or_ge |j| l with hj | hj
  · rw [hφl j hj _ k.2, zero_mul]
  · rw [hψl (-j) (by rwa [abs_neg]) _ k.2, mul_zero]

end RealBlockTransposition

end Langlands.Archimedean
