import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealBlockMultiplier
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-!
# Block Fourier multiplier functionals as real Jacquet functionals

On the `O(n)`-finite functions `V` of the real standard module of a list of real blocks `ds`,
the functional `ℓ_μ(f) = (2π)⁻¹ Σᶠ_j μ_j Φ_j(f)(1)` weights the block Fourier coefficients
`Φ_j = blockFourierCoefficient n p j` at the identity by a multiplier `μ : ℤ → ℂ`.

* `finsum_rightDerivative`: if `μ` satisfies the recurrence `IsRecurrent δ ε μ` with
  `δ = α_p - α_{p+1}` and `ε` the parity class of the surviving modes, then
  `ℓ_μ(R_A f) = (Σ_i α_i A_ii - (δ - 1)(A_pp - A_{p+1,p+1})) ℓ_μ(f)` for every upper triangular
  `A`.
* `blockJacquet_signReflection`: if `μ` is symmetric (`IsSymmetric ε σ μ`), the sign matrices
  act on `ℓ_μ` by `χ_i(-1) σ` inside the block and by `χ_i(-1)` outside.
* `isRealJacquetFunctional_blockJacquet`: together, `ℓ_μ` is a real Jacquet functional whose
  exponents are those of `ds` with the two block exponents exchanged (shifted by `± 1`).
* `blockFourierCoefficient_frobFun`: the Frobenius function of `ℓ_μ` multiplies the block
  Fourier coefficients by `μ` on `O(n)`; `blockFourierCoefficient_frobFun_eq_zero`: it keeps the
  vanishing of the Fourier coefficients along a disjoint block.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealBlockJacquet

open RealBlockRotation RealBlockFourierFinite RealBlockDerivative RealBlockMultiplier
open Langlands.LocalFactor.Archimedean

/-! ## Rotations outside the range -/

section Degenerate

variable {N p : ℕ}

theorem rotationGenerator_eq_zero (h : ¬ p + 1 < N) : rotationGenerator N p = 0 := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [rotationGenerator, Matrix.of_apply, Matrix.zero_apply]
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

theorem blockRotation_eq_one (h : ¬ p + 1 < N) (θ : ℝ) : blockRotation N p θ = 1 := by
  ext1
  rw [blockRotation_val, rotationGenerator_eq_zero h, smul_zero, NormedSpace.exp_zero,
    Units.val_one]

/-- For `p + 1 ≥ N` the rotation is trivial and only the coefficient of index `0` survives. -/
theorem blockFourierCoefficient_of_not_lt (h : ¬ p + 1 < N) (k : ℤ)
    (f : Langlands.GeneralLinear N ℝ → ℂ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k f g = if k = 0 then 2 * (Real.pi : ℂ) * f g else 0 := by
  have e : (fun θ : ℝ => f (blockRotation N p θ * g)) = f g • expMode 0 := by
    funext θ
    simp [blockRotation_eq_one h, expMode_zero_left]
  rw [blockFourierCoefficient_eq_coeff, e, coeff_smul, coeff_expMode]
  split_ifs <;> first | omega | ring

/-- A bound on the Fourier modes on `O(N)` of a continuous right `O(N)`-finite function, for
every `p`. -/
theorem exists_bound (p : ℕ) {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) :
    ∃ D : ℕ, ∀ j : ℤ, (D : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j f g = 0 := by
  by_cases hp : p + 1 < N
  · exact exists_blockFourierCoefficient_eq_zero hp hf hK
  · refine ⟨0, fun j hj g _ => ?_⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp at hj
    rw [blockFourierCoefficient_of_not_lt hp]
    simp [hj0]

end Degenerate

/-! ## Elementary facts -/

theorem finite_support_of_bound {F : ℤ → ℂ} (D : ℕ) (h : ∀ j : ℤ, (D : ℤ) < |j| → F j = 0) :
    (Function.support F).Finite := by
  refine (Finset.Icc (-(D : ℤ)) D).finite_toSet.subset fun j hj => ?_
  rw [Finset.coe_Icc, Set.mem_Icc, ← abs_le]
  by_contra hlt
  exact hj (h j (not_le.mp hlt))

theorem lt_abs_add {D : ℕ} {j m : ℤ} (hm : |m| ≤ 2) (h : ((D + 2 : ℕ) : ℤ) < |j|) :
    (D : ℤ) < |j + m| := by
  rw [abs_le] at hm
  push_cast at h
  rcases lt_abs.mp h with h | h <;> exact lt_abs.mpr (by omega)

theorem neg_one_pow_fin_add (a b : Fin 2) :
    (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  fin_cases a <;> fin_cases b <;> simp

theorem blockFourierCoefficient_add {N : ℕ} (p : ℕ) (k : ℤ)
    {f₁ f₂ : Langlands.GeneralLinear N ℝ → ℂ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (f₁ + f₂) g =
      blockFourierCoefficient N p k f₁ g + blockFourierCoefficient N p k f₂ g := by
  unfold blockFourierCoefficient
  simp only [Pi.add_apply, add_mul]
  exact intervalIntegral.integral_add (intervalIntegrable_blockFourier h₁ p k g _ _)
    (intervalIntegrable_blockFourier h₂ p k g _ _)

theorem blockFourierCoefficient_smul {N : ℕ} (p : ℕ) (k : ℤ) (c : ℂ)
    (f : Langlands.GeneralLinear N ℝ → ℂ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (c • f) g = c * blockFourierCoefficient N p k f g := by
  unfold blockFourierCoefficient
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact intervalIntegral.integral_const_mul c _

theorem blockFourierCoefficient_zero_fun {N : ℕ} (p : ℕ) (k : ℤ)
    (g : Langlands.GeneralLinear N ℝ) : blockFourierCoefficient N p k 0 g = 0 := by
  simp [blockFourierCoefficient]

/-- The block Fourier coefficients of a continuous function are continuous. -/
theorem continuous_blockFourierCoefficient {N : ℕ} (p : ℕ) (k : ℤ)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f) :
    Continuous (blockFourierCoefficient N p k f) := by
  unfold blockFourierCoefficient
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (g : Langlands.GeneralLinear N ℝ) (θ : ℝ) =>
      f (blockRotation N p θ * g) * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) ?_ _ _
  refine (hf.comp ?_).mul ?_
  · exact ((continuous_blockRotation N p).comp continuous_snd).mul continuous_fst
  · exact Complex.continuous_exp.comp (by fun_prop)

/-- Fourier coefficients of a finite sum of continuous functions. -/
theorem coeff_finset_sum (I : Finset ℤ) (F : ℤ → ℝ → ℂ) (hF : ∀ i ∈ I, Continuous (F i))
    (k : ℤ) : coeff k (fun θ => ∑ i ∈ I, F i θ) = ∑ i ∈ I, coeff k (F i) := by
  unfold coeff
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i hi => intervalIntegrable_coeff (hF i hi) k _ _

theorem coeff_const_mul (c : ℂ) (F : ℝ → ℂ) (k : ℤ) :
    coeff k (fun θ => c * F θ) = c * coeff k F :=
  coeff_smul c F k

/-- Fourier coefficients of a trigonometric polynomial given by its coefficients. -/
theorem coeff_finset_sum_expMode (I : Finset ℤ) (c : ℤ → ℂ) (k : ℤ) :
    coeff k (fun θ => ∑ i ∈ I, c i * expMode i θ) =
      if k ∈ I then c k * (2 * (Real.pi : ℂ)) else 0 := by
  rw [coeff_finset_sum I (fun i θ => c i * expMode i θ)
    fun i _ => continuous_const.mul (continuous_expMode i)]
  simp_rw [coeff_const_mul, coeff_expMode, mul_ite, mul_zero]
  exact Finset.sum_ite_eq' I k _

/-! ## The functions of the standard module -/

section Standard

variable {n : ℕ} {ds : List RealBlock}

theorem continuous_coe (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    Continuous (f : Langlands.GeneralLinear n ℝ → ℂ) :=
  (contMDiff_of_mem_realStandardModule f.2.1).continuous

theorem exists_bound_coe (p : ℕ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    ∃ D : ℕ, ∀ j : ℤ, (D : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n p j f g = 0 :=
  exists_bound p (continuous_coe f) f.2.2

theorem finite_support_mul (p : ℕ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) (F : ℤ → ℂ)
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    (Function.support fun j => F j * blockFourierCoefficient n p j f g).Finite := by
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  exact finite_support_of_bound D fun j hj => by rw [hD j hj g hg, mul_zero]

/-- Modes outside the parity class `ε` vanish, when `(-1)^ε = χ_p(-1) χ_{p+1}(-1)`. -/
theorem blockFourierCoefficient_eq_zero_of_not_even {p : ℕ} (hp : p + 1 < n) {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1))
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) {j : ℤ}
    (hj : ¬ Even (j - ε)) (g : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n p j f g = 0 := by
  refine blockFourierCoefficient_eq_zero_of_parity hp (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds) f.2.1.1 ?_ g
  rw [← hpar]
  intro h
  have hodd : Odd (j - ε) := Int.not_even_iff_odd.mp hj
  have h1 : (-1 : ℂ) ^ j = -(-1 : ℂ) ^ ε := by
    rw [show j = (j - ε) + ε by ring, zpow_add₀ (by norm_num), hodd.neg_one_zpow, neg_one_mul]
  rw [h1] at h
  have h0 : (-1 : ℂ) ^ ε ≠ 0 := zpow_ne_zero _ (by norm_num)
  exact h0 (by linear_combination (-1 / 2 : ℂ) * h)

end Standard

/-! ## The functional -/

/-- The block Jacquet functional `ℓ_μ(f) = (2π)⁻¹ Σᶠ_j μ_j Φ_j(f)(1)` on the `O(n)`-finite
functions of the real standard module of `ds`, with `Φ_j = blockFourierCoefficient n p j`. -/
def blockJacquet (n : ℕ) (ds : List RealBlock) (p : ℕ) (μ : ℤ → ℂ) :
    kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ where
  toFun f := (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j f 1
  map_add' f₁ f₂ := by
    rw [← mul_add, ← finsum_add_distrib (finite_support_mul p f₁ μ (one_mem _))
      (finite_support_mul p f₂ μ (one_mem _))]
    congr 2
    funext j
    rw [Submodule.coe_add, blockFourierCoefficient_add p j (continuous_coe f₁)
      (continuous_coe f₂), mul_add]
  map_smul' c f := by
    change (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j
        (c • (f : Langlands.GeneralLinear n ℝ → ℂ)) 1 =
      c * ((2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j f 1)
    simp only [blockFourierCoefficient_smul]
    rw [mul_left_comm c, mul_finsum _ c]
    congr 2
    funext j
    ring

section Functional

variable {n : ℕ} {ds : List RealBlock} {p : ℕ} {μ : ℤ → ℂ}

theorem blockJacquet_apply (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockJacquet n ds p μ f =
      (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j f 1 :=
  rfl

/-- The algebra of the tridiagonal formula: if `c` has bounded support, vanishes off the parity
class `ε` and `μ` satisfies the recurrence for `δ`, then the multiplier sum of the tridiagonal
combination is `S - (δ - 1)(x - y)` times the multiplier sum of `c`. -/
theorem finsum_tridiagonal {μ c : ℤ → ℂ} {δ : ℂ} {ε : ℤ} (D : ℕ)
    (hc : ∀ j : ℤ, (D : ℤ) < |j| → c j = 0) (hpar : ∀ j, ¬ Even (j - ε) → c j = 0)
    (hrec : IsRecurrent δ ε μ) (S x y v : ℂ) :
    ∑ᶠ j : ℤ, μ j * ((S - δ * (x - y) / 2 - Complex.I * v * j / 2) * c j +
        (x - y + Complex.I * v) / 4 * (δ + j - 2) * c (j - 2) +
        (x - y - Complex.I * v) / 4 * (δ - j - 2) * c (j + 2)) =
      (S - (δ - 1) * (x - y)) * ∑ᶠ j : ℤ, μ j * c j := by
  have hc2 : ∀ j : ℤ, ((D + 2 : ℕ) : ℤ) < |j| → c (j - 2) = 0 := fun j hj =>
    hc _ (by rw [sub_eq_add_neg]; exact lt_abs_add (by norm_num) hj)
  have hc2' : ∀ j : ℤ, ((D + 2 : ℕ) : ℤ) < |j| → c (j + 2) = 0 := fun j hj =>
    hc _ (lt_abs_add (by norm_num) hj)
  set F₁ : ℤ → ℂ := fun j => μ j * ((S - δ * (x - y) / 2 - Complex.I * v * j / 2) * c j)
    with hF₁
  set F₂ : ℤ → ℂ := fun j => μ j * ((x - y + Complex.I * v) / 4 * (δ + j - 2) * c (j - 2))
    with hF₂
  set F₃ : ℤ → ℂ := fun j => μ j * ((x - y - Complex.I * v) / 4 * (δ - j - 2) * c (j + 2))
    with hF₃
  set G₂ : ℤ → ℂ := fun j => μ (j + 2) * ((x - y + Complex.I * v) / 4 * (δ + j) * c j)
    with hG₂
  set G₃ : ℤ → ℂ := fun j => μ (j - 2) * ((x - y - Complex.I * v) / 4 * (δ - j) * c j)
    with hG₃
  have h₁ : (Function.support F₁).Finite :=
    finite_support_of_bound D fun j hj => by simp [F₁, hc j hj]
  have h₂ : (Function.support F₂).Finite :=
    finite_support_of_bound (D + 2) fun j hj => by simp [F₂, hc2 j hj]
  have h₃ : (Function.support F₃).Finite :=
    finite_support_of_bound (D + 2) fun j hj => by simp [F₃, hc2' j hj]
  have k₂ : (Function.support G₂).Finite :=
    finite_support_of_bound D fun j hj => by simp [G₂, hc j hj]
  have k₃ : (Function.support G₃).Finite :=
    finite_support_of_bound D fun j hj => by simp [G₃, hc j hj]
  have e₂ : ∑ᶠ j : ℤ, F₂ j = ∑ᶠ j : ℤ, G₂ j := by
    rw [← finsum_comp_equiv (Equiv.addRight (2 : ℤ)) (f := F₂)]
    congr 1
    funext j
    simp only [Equiv.coe_addRight, F₂, G₂, add_sub_cancel_right]
    push_cast
    ring
  have e₃ : ∑ᶠ j : ℤ, F₃ j = ∑ᶠ j : ℤ, G₃ j := by
    rw [← finsum_comp_equiv (Equiv.subRight (2 : ℤ)) (f := F₃)]
    congr 1
    funext j
    simp only [Equiv.subRight_apply, F₃, G₃, sub_add_cancel]
    push_cast
    ring
  have hsplit : (fun j : ℤ => μ j * ((S - δ * (x - y) / 2 - Complex.I * v * j / 2) * c j +
        (x - y + Complex.I * v) / 4 * (δ + j - 2) * c (j - 2) +
        (x - y - Complex.I * v) / 4 * (δ - j - 2) * c (j + 2))) =
      fun j => F₁ j + F₂ j + F₃ j := by
    funext j
    simp only [F₁, F₂, F₃]
    ring
  rw [hsplit, finsum_add_distrib ((h₁.union h₂).subset (Function.support_add _ _)) h₃,
    finsum_add_distrib h₁ h₂, e₂, e₃, ← finsum_add_distrib h₁ k₂,
    ← finsum_add_distrib ((h₁.union k₂).subset (Function.support_add _ _)) k₃, mul_finsum]
  congr 1
  funext j
  simp only [F₁, G₂, G₃]
  by_cases hj : Even (j - ε)
  · have r1 := hrec j hj
    have hj2 : Even (j - 2 - ε) := by
      rw [show j - 2 - ε = (j - ε) - 2 by ring]
      exact hj.sub even_two
    have r2 := hrec (j - 2) hj2
    rw [sub_add_cancel] at r2
    push_cast at r1 r2
    linear_combination c j * (x - y + Complex.I * v) / 4 * r1 +
      c j * (x - y - Complex.I * v) / 4 * r2
  · simp [hpar j hj]

/-- **The functional on right derivatives.** For an upper triangular `A`,
`ℓ_μ(R_A f) = (Σ_i α_i A_ii - (δ - 1)(A_pp - A_{p+1,p+1})) ℓ_μ(f)` up to the factor `(2π)⁻¹`,
where `α_i = τ_i + (n - 1)/2 - i` and `δ = α_p - α_{p+1}`, provided `μ` satisfies the recurrence
for `δ` on the parity class `ε` of the modes. -/
theorem finsum_rightDerivative (hp : p + 1 < n) {τ : Fin n → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1))
    (hrec : IsRecurrent ((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
      (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) ε μ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsUpperTriangular) :
    ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j (rightDerivative (matrixModel ℝ n) A f) 1 =
      (∑ i, (τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) * (A i i : ℂ) -
        ((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ)) - 1) *
          ((A (ia hp) (ia hp) : ℂ) - A (ib hp) (ib hp))) *
        ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j f 1 := by
  have hα := isExpEquivariant_of_mem_principalSeries hτ f.2.1.1
  have hsm := contMDiff_of_mem_realStandardModule f.2.1
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  simp_rw [blockFourierCoefficient_rightDerivative hp hsm hα hA (X := A) 1 (by simp)]
  exact finsum_tridiagonal D (fun j hj => hD j hj 1 (one_mem _))
    (fun j hj => blockFourierCoefficient_eq_zero_of_not_even hp hpar f hj 1) hrec _ _ _ _

/-! ## Signs -/

/-- **Signs.** If `μ` is symmetric for `σ` on the parity class `ε` of the modes, the sign
matrix `s_i` acts on `ℓ_μ` by `χ_i(-1) σ` for `i ∈ {p, p + 1}` and by `χ_i(-1)` otherwise. -/
theorem blockJacquet_signReflection (hp : p + 1 < n) {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1))
    {σ : ℂ} (hsym : IsSymmetric ε σ μ) (i : Fin n)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockJacquet n ds p μ (realStandardRep n ds (signReflection n i) f) =
      (if (i : ℕ) = p ∨ (i : ℕ) = p + 1 then realPositionCharacter ds i (-1) * σ
        else realPositionCharacter ds i (-1)) * blockJacquet n ds p μ f := by
  rw [blockJacquet_apply, blockJacquet_apply, realStandardRep_apply_coe]
  simp_rw [blockFourierCoefficient_rightTranslation, one_mul]
  split_ifs with hi
  · have hΦ : ∀ k : ℤ, blockFourierCoefficient n p k f (Unitary.toUnits (signReflection n i)) =
        realPositionCharacter ds i (-1) * blockFourierCoefficient n p (-k) f 1 := fun k => by
      have := blockFourierCoefficient_signReflection_mul_of_mem hp (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds)
        f.2.1.1 i hi k 1
      rwa [mul_one] at this
    simp_rw [hΦ]
    have e1 : ∑ᶠ k : ℤ, μ k * (realPositionCharacter ds i (-1) *
          blockFourierCoefficient n p (-k) f 1) =
        ∑ᶠ k : ℤ, μ (-k) * (realPositionCharacter ds i (-1) *
          blockFourierCoefficient n p k f 1) := by
      rw [← finsum_comp_equiv (Equiv.neg ℤ) (f := fun k : ℤ => μ (-k) *
        (realPositionCharacter ds i (-1) * blockFourierCoefficient n p k f 1))]
      simp only [Equiv.neg_apply, neg_neg]
    have e2 : ∀ k : ℤ, μ (-k) * (realPositionCharacter ds i (-1) *
          blockFourierCoefficient n p k f 1) =
        realPositionCharacter ds i (-1) * σ * (μ k * blockFourierCoefficient n p k f 1) := by
      intro k
      by_cases hk : Even (k - ε)
      · rw [hsym k hk]
        ring
      · rw [blockFourierCoefficient_eq_zero_of_not_even hp hpar f hk 1]
        ring
    rw [e1]
    simp_rw [e2]
    rw [← mul_finsum]
    ring
  · have hi' : (i : ℕ) ≠ p ∧ (i : ℕ) ≠ p + 1 := not_or.mp hi
    have hΦ : ∀ k : ℤ, blockFourierCoefficient n p k f (Unitary.toUnits (signReflection n i)) =
        realPositionCharacter ds i (-1) * blockFourierCoefficient n p k f 1 := fun k => by
      have := blockFourierCoefficient_signReflection_mul_of_not_mem hp
        (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds) f.2.1.1 i hi' k 1
      rwa [mul_one] at this
    simp_rw [hΦ, mul_left_comm (μ _)]
    rw [← mul_finsum]
    ring

/-- The sign hypothesis of the Frobenius function (`frobFun_eq`) for `ℓ_μ`, from the symmetry
of `μ` alone: the signs `e` satisfy `(-1)^{e_i} = χ_i(-1)` off the block and
`(-1)^{e_i} = χ_i(-1) σ` on it. -/
theorem blockJacquet_hsign (hp : p + 1 < n) {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1))
    {σ : ℂ} (hsym : IsSymmetric ε σ μ) {e : Fin n → Fin 2}
    (he_off : ∀ i : Fin n, i ≠ ia hp → i ≠ ib hp →
      (-1 : ℂ) ^ (e i).val = realPositionCharacter ds i (-1))
    (he_p : (-1 : ℂ) ^ (e (ia hp)).val = realPositionCharacter ds p (-1) * σ)
    (he_q : (-1 : ℂ) ^ (e (ib hp)).val = realPositionCharacter ds (p + 1) (-1) * σ)
    (i : Fin n) (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockJacquet n ds p μ (realStandardRep n ds (signReflection n i) f) =
      (-1 : ℂ) ^ (e i).val * blockJacquet n ds p μ f := by
  rw [blockJacquet_signReflection hp hpar hsym i f]
  congr 1
  split_ifs with hi
  · rcases hi with hi | hi
    · have : i = ia hp := Fin.ext hi
      subst this
      exact he_p.symm
    · have : i = ib hp := Fin.ext hi
      subst this
      exact he_q.symm
  · refine (he_off i (fun h => hi (Or.inl ?_)) (fun h => hi (Or.inr ?_))).symm
    · rw [h]; rfl
    · rw [h]; rfl

/-! ## The real Jacquet functional -/

/-- **`ℓ_μ` is a real Jacquet functional.** Let `χ = realPositionCharacter ds` with
`χ_i(e^x) = e^{τ_i x}`, `α_i = τ_i + (n - 1)/2 - i` and `δ = α_p - α_{p+1}`. Let the modes of
`ds` at the block `p, p + 1` live on the parity class `ε` (`(-1)^ε = χ_p(-1) χ_{p+1}(-1)`), and
let `μ` satisfy the recurrence for `δ` and the symmetry for `σ` on it. Then `ℓ_μ` is a real
Jacquet functional with exponents `a` and signs `e`, for `a` equal to `α` off the block,
`a_p = α_{p+1} + 1`, `a_{p+1} = α_p - 1`, and signs `e` with `(-1)^{e_i} = χ_i(-1)` off the
block and `(-1)^{e_i} = χ_i(-1) σ` on it. -/
theorem isRealJacquetFunctional_blockJacquet (hp : p + 1 < n) {τ : Fin n → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1))
    (hrec : IsRecurrent ((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
      (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) ε μ)
    {σ : ℂ} (hsym : IsSymmetric ε σ μ) {a : Fin n → ℂ}
    (ha_off : ∀ i : Fin n, i ≠ ia hp → i ≠ ib hp →
      a i = τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))
    (ha_p : a (ia hp) = τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ) + 1)
    (ha_q : a (ib hp) = τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ) - 1)
    {e : Fin n → Fin 2}
    (he_off : ∀ i : Fin n, i ≠ ia hp → i ≠ ib hp →
      (-1 : ℂ) ^ (e i).val = realPositionCharacter ds i (-1))
    (he_p : (-1 : ℂ) ^ (e (ia hp)).val = realPositionCharacter ds p (-1) * σ)
    (he_q : (-1 : ℂ) ^ (e (ib hp)).val = realPositionCharacter ds (p + 1) (-1) * σ) :
    IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
      (blockJacquet n ds p μ) a e := by
  refine ⟨fun X hX f => ?_, fun i f => ⟨?_, blockJacquet_hsign hp hpar hsym he_off he_p he_q i f⟩⟩
  · have hU : X.IsUpperTriangular := fun i k hik => hX i k (le_of_lt hik)
    have hdiag : ∀ i, X i i = 0 := fun i => hX i i le_rfl
    rw [blockJacquet_apply, realStandardLie_one_tmul_apply_coe,
      finsum_rightDerivative hp hτ hpar hrec f hU]
    simp [hdiag]
  · have hU : (Matrix.single i i (1 : ℝ)).IsUpperTriangular := fun k l hkl => by
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hkl
    rw [blockJacquet_apply, blockJacquet_apply, realStandardLie_one_tmul_apply_coe,
      finsum_rightDerivative hp hτ hpar hrec f hU]
    have hsum : ∑ k, (τ k + ((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ)) *
        ((Matrix.single i i (1 : ℝ) k k : ℝ) : ℂ) = τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hk h.1.symm)]
        simp
      · simp
    rw [hsum]
    have hne := ia_ne_ib hp
    have key : τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) -
        ((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ)) - 1) *
          (((Matrix.single i i (1 : ℝ) (ia hp) (ia hp) : ℝ) : ℂ) -
            ((Matrix.single i i (1 : ℝ) (ib hp) (ib hp) : ℝ) : ℂ)) = a i := by
      by_cases h1 : i = ia hp
      · subst h1
        rw [ha_p, Matrix.single_apply_same,
          Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hne h.1)]
        push_cast
        ring
      · by_cases h2 : i = ib hp
        · subst h2
          rw [ha_q, Matrix.single_apply_same,
            Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hne h.1.symm)]
          push_cast
          ring
        · rw [ha_off i h1 h2, Matrix.single_apply_of_ne _ _ _ _ _ (fun h => h1 h.1),
            Matrix.single_apply_of_ne _ _ _ _ _ (fun h => h2 h.1)]
          push_cast
          ring
    rw [key]
    ring

/-! ## The Frobenius function of `ℓ_μ` -/

/-- On `O(n)` the Frobenius function of `ℓ_μ` is `g ↦ ℓ_μ(R_g f) = (2π)⁻¹ Σᶠ_i μ_i Φ_i(f)(g)`. -/
theorem frobFun_apply_of_mem {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (hsign : ∀ (j : Fin n) (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      blockJacquet n ds p μ (realStandardRep n ds (signReflection n j) v) =
        (-1) ^ (e j).val * blockJacquet n ds p μ v)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds p μ) a e f g =
      (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ i : ℤ, μ i * blockFourierCoefficient n p i f g := by
  rw [RealJacquetFrobenius.frobFun_eq hsign (b := 1) (k := (g : Matrix (Fin n) (Fin n) ℝ))
    Matrix.blockTriangular_one hg (one_mul _).symm f, RealJacquetFrobenius.diagChar_one, one_mul,
    blockJacquet_apply, realStandardRep_apply_coe]
  have hu : (Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) : Langlands.GeneralLinear n ℝ) = g := Units.ext rfl
  simp_rw [blockFourierCoefficient_rightTranslation, one_mul, hu]

/-- **Multiplier on `O(n)`.** For `k ∈ O(n)`, the block Fourier coefficients of the Frobenius
function of `ℓ_μ` are `Φ_j(B f)(k) = μ_j Φ_j(f)(k)`. -/
theorem blockFourierCoefficient_frobFun (hp : p + 1 < n) {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (hsign : ∀ (j : Fin n) (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      blockJacquet n ds p μ (realStandardRep n ds (signReflection n j) v) =
        (-1) ^ (e j).val * blockJacquet n ds p μ v)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) (j : ℤ) :
    blockFourierCoefficient n p j
        (RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds p μ) a e f) k =
      μ j * blockFourierCoefficient n p j f k := by
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  set I : Finset ℤ := Finset.Icc (-(D : ℤ)) D with hI
  have hout : ∀ i : ℤ, i ∉ I → blockFourierCoefficient n p i f k = 0 := by
    intro i hi
    refine hD i ?_ k hk
    rw [hI, Finset.mem_Icc, ← abs_le] at hi
    exact not_le.mp hi
  have horb : (fun θ : ℝ => RealJacquetFrobenius.frobFun (realStandardRep n ds)
      (blockJacquet n ds p μ) a e f (blockRotation n p θ * k)) =
      fun θ => ∑ i ∈ I, (2 * (Real.pi : ℂ))⁻¹ * (μ i * blockFourierCoefficient n p i f k) *
        expMode i θ := by
    funext θ
    rw [frobFun_apply_of_mem hsign f
      ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hk)]
    simp_rw [blockFourierCoefficient_blockRotation_mul hp]
    rw [finsum_eq_sum_of_support_subset (s := I), Finset.mul_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [expMode]
      ring
    · intro i hi
      by_contra hiI
      exact hi (by simp [hout i hiI])
  rw [blockFourierCoefficient_eq_coeff, horb, coeff_finset_sum_expMode]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  split_ifs with hj
  · field_simp
  · rw [hout j hj, mul_zero]

/-- **Disjoint blocks.** If the Fourier coefficient `Φ^{p'}_i f` along a block `p'` disjoint
from `p` vanishes identically, then so does `Φ^{p'}_i` of the Frobenius function of `ℓ_μ`, on
`O(n)`. -/
theorem blockFourierCoefficient_frobFun_eq_zero {p' : ℕ} (hd : p + 1 < p' ∨ p' + 1 < p)
    {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (hsign : ∀ (j : Fin n) (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      blockJacquet n ds p μ (realStandardRep n ds (signReflection n j) v) =
        (-1) ^ (e j).val * blockJacquet n ds p μ v)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) (i : ℤ)
    (h0 : ∀ g, blockFourierCoefficient n p' i f g = 0)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n p' i
        (RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds p μ) a e f) k =
      0 := by
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  set I : Finset ℤ := Finset.Icc (-(D : ℤ)) D with hI
  have horb : (fun φ : ℝ => RealJacquetFrobenius.frobFun (realStandardRep n ds)
      (blockJacquet n ds p μ) a e f (blockRotation n p' φ * k)) =
      fun φ => ∑ j ∈ I, (2 * (Real.pi : ℂ))⁻¹ * μ j *
        blockFourierCoefficient n p j f (blockRotation n p' φ * k) := by
    funext φ
    have hm := (unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p' φ) hk
    rw [frobFun_apply_of_mem hsign f hm, finsum_eq_sum_of_support_subset (s := I),
      Finset.mul_sum]
    · simp_rw [mul_assoc]
    · intro j hj
      by_contra hjI
      refine hj ?_
      have hj' : (D : ℤ) < |j| := by
        rw [hI, Finset.coe_Icc, Set.mem_Icc, ← abs_le] at hjI
        exact not_le.mp hjI
      simp [hD j hj' _ hm]
  have hzero : blockFourierCoefficient n p' i (f : Langlands.GeneralLinear n ℝ → ℂ) = 0 :=
    funext h0
  rw [blockFourierCoefficient_eq_coeff, horb, coeff_finset_sum I
    (fun j φ => (2 * (Real.pi : ℂ))⁻¹ * μ j *
      blockFourierCoefficient n p j f (blockRotation n p' φ * k)) fun j _ =>
    continuous_const.mul ((continuous_blockFourierCoefficient p j (continuous_coe f)).comp
      ((continuous_blockRotation n p').mul continuous_const))]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_const_mul]
  have hc : coeff i (fun φ => blockFourierCoefficient n p j f (blockRotation n p' φ * k)) =
      blockFourierCoefficient n p' i (blockFourierCoefficient n p j f) k := rfl
  rw [hc, ← blockFourierCoefficient_comm hd (continuous_coe f), hzero,
    blockFourierCoefficient_zero_fun, mul_zero]

end Functional

end RealBlockJacquet

end Langlands.Archimedean
