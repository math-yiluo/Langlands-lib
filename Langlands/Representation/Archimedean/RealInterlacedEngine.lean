import Langlands.Representation.Archimedean.RealInterlacedChain

/-!
# The engine of the chain for two interlaced induction blocks

The test functions `G± = y^r ν±^m` built from a column `y` and the self-dual Plücker
coordinates `ν±`, their test vectors in the standard module of two induction blocks, and the
main evaluation `main_value`: after a tail step at the middle block and a generic step at an
outer block, the sign multiplier at the middle block has an explicit nonzero Fourier
coefficient, once the window of the middle block vanishes.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInterlacedJacquet

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealBlockDerivative RealCharacterCrossing RealBlockFlatJacquet InductionStages

variable {n : ℕ}

/-! ## Generic lemmas -/

section Generic

theorem finsum_sign_two {N : ℤ} (hN : 0 < N) (c : ℤ → ℂ)
    (h : ∀ j : ℤ, j ≠ N → j ≠ -N → c j = 0) :
    ∑ᶠ j : ℤ, ((Int.sign j : ℤ) : ℂ) * c j = c N - c (-N) := by
  have h1 : N ≠ -N := by omega
  rw [finsum_eq_sum_of_support_subset (s := {N, -N}) _ ?_]
  · rw [Finset.sum_pair h1, Int.sign_eq_one_of_pos hN, Int.sign_eq_neg_one_of_neg (by omega)]
    push_cast
    ring
  · intro j hj
    rw [Function.mem_support] at hj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra h'
    push Not at h'
    exact hj (by rw [h j h'.1 h'.2, mul_zero])

/-- **A flat step on two modes.** If `w` has the two modes `±N` along the block `b` through every
point of `SO(n)`, the Frobenius map of `ℓ_μ` takes there the value `μ_N A + μ_{-N} B`. -/
theorem frobMap_eq_two_mode {ds' : List RealBlock} {b : ℕ} {μ : ℤ → ℂ} {a : Fin n → ℂ}
    {e : Fin n → Fin 2}
    (hJ : IsRealJacquetFunctional n (realStandardRep n ds') (realStandardLie n ds')
      (blockJacquet n ds' b μ) a e) (w : KF n ds') {N : ℤ} (hN : N ≠ 0) {A B : MF n}
    (hw : ∀ κ ∈ SOset n, ∀ φ : ℝ, (w : Langlands.GeneralLinear n ℝ → ℂ)
      (blockRotation n b φ * κ) = expMode N φ * A (κ : Matrix (Fin n) (Fin n) ℝ) +
        expMode (-N) φ * B (κ : Matrix (Fin n) (Fin n) ℝ))
    {κ : Langlands.GeneralLinear n ℝ} (hκ : κ ∈ SOset n) :
    ((frobMap hJ w : KF n _) : Langlands.GeneralLinear n ℝ → ℂ) κ =
      μ N * A (κ : Matrix (Fin n) (Fin n) ℝ) + μ (-N) * B (κ : Matrix (Fin n) (Fin n) ℝ) := by
  rw [frobMap_coe, frobFun_apply_of_mem (fun j v => (hJ.2 j v).2) w hκ.1,
    finsum_blockFourier_two_mode hN (hw κ hκ) μ]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

theorem continuous_binom (σ : ℤ) (a b : ℂ) (N : ℕ) :
    Continuous fun t : ℝ => (a * expMode σ t + b) ^ N :=
  ((continuous_const.mul (continuous_expMode σ)).add continuous_const).pow N

/-- Fourier coefficients of a combination of two binomial powers. -/
theorem coeff_binom_pair {σ : ℤ} (hσ : σ ≠ 0) (a₁ b₁ a₂ b₂ c₁ c₂ : ℂ) (N : ℕ) {j : ℕ}
    (hj : j ≤ N) :
    coeff (σ * j) (fun t => c₁ * (a₁ * expMode σ t + b₁) ^ N + c₂ * (a₂ * expMode σ t + b₂) ^ N) =
      2 * (Real.pi : ℂ) * (N.choose j : ℂ) *
        (c₁ * (a₁ ^ j * b₁ ^ (N - j)) + c₂ * (a₂ ^ j * b₂ ^ (N - j))) := by
  have e : (fun t => c₁ * (a₁ * expMode σ t + b₁) ^ N + c₂ * (a₂ * expMode σ t + b₂) ^ N) =
      (fun t => c₁ * (a₁ * expMode σ t + b₁) ^ N) + fun t => c₂ * (a₂ * expMode σ t + b₂) ^ N :=
    rfl
  have h1 : Continuous fun t : ℝ => c₁ * (a₁ * expMode σ t + b₁) ^ N :=
    continuous_const.mul (continuous_binom σ a₁ b₁ N)
  have h2 : Continuous fun t : ℝ => c₂ * (a₂ * expMode σ t + b₂) ^ N :=
    continuous_const.mul (continuous_binom σ a₂ b₂ N)
  rw [e, coeff_add (F := fun t => c₁ * (a₁ * expMode σ t + b₁) ^ N)
    (G := fun t => c₂ * (a₂ * expMode σ t + b₂) ^ N) h1 h2,
    coeff_const_mul c₁ (fun t => (a₁ * expMode σ t + b₁) ^ N),
    coeff_const_mul c₂ (fun t => (a₂ * expMode σ t + b₂) ^ N),
    coeff_binom hσ _ _ _ hj, coeff_binom hσ _ _ _ hj]
  ring

end Generic

/-! ## The main evaluation -/

section Main

/-- **The main evaluation.** Let `w₀` agree on `SO(4)` with `H₁ ∈ S = L_y^r L_w^m`, let `ℓ₁` be a
Jacquet functional at the middle block and `ℓ₂` one at an outer block `b₂` with a multiplier
without zeros, and let `w = Ψ₂ Ψ₁ w₀` for their Frobenius maps. Suppose that the window
`|j| + 1 < r + m` of `w` at the middle block vanishes on `O(4)`, that the parity class of the
middle block is that of `r + m`, and that `ℓ₁` does not kill the mode `j*` of `H₁` along
`r₁(t) κ₀`. Then the top coefficient of `w` at the middle block is `g T` with `g ≠ 0`, and
`θ ↦ Σᶠ_j sgn(j) Φ^{(1)}_j(w)(r_{r_b}(θ))` is `2π g (T(r(θ)) ∓ T(s₃ s₂ r(θ)))`: the hypothesis
`hfin` on these functions gives a nonzero Fourier coefficient. -/
theorem main_value {ds0 : List RealBlock} {u u' : Fin 4 → ℂ} {r m b2 rb : ℕ} (hrm : 0 < r + m)
    (hb2 : b2 + 1 < 4) (hS2 : HasExpTop b2 (r + m) (Sm u u' r m) ⊤)
    {μ1 : ℤ → ℂ} {a1 : Fin 4 → ℂ} {e1 : Fin 4 → Fin 2}
    (hJ1 : IsRealJacquetFunctional 4 (realStandardRep 4 ds0) (realStandardLie 4 ds0)
      (blockJacquet 4 ds0 1 μ1) a1 e1)
    {μ2 : ℤ → ℂ} {a2 : Fin 4 → ℂ} {e2 : Fin 4 → Fin 2}
    (hJ2 : IsRealJacquetFunctional 4 (realStandardRep 4 (PL (RealJacquetFrobenius.expo a1) e1))
      (realStandardLie 4 (PL (RealJacquetFrobenius.expo a1) e1))
      (blockJacquet 4 (PL (RealJacquetFrobenius.expo a1) e1) b2 μ2) a2 e2)
    (hμ2 : ∀ j, μ2 j ≠ 0)
    {H1 : MF 4} (hH1 : H1 ∈ Sm u u' r m) (w0 : KF 4 ds0)
    (hw0 : ∀ κ ∈ SOset 4,
      (w0 : Langlands.GeneralLinear 4 ℝ → ℂ) κ = H1 (κ : Matrix (Fin 4) (Fin 4) ℝ))
    {κ0 : Langlands.GeneralLinear 4 ℝ} (hκ0 : κ0 ∈ SOset 4) {jst : ℤ} (hμ1 : μ1 jst ≠ 0)
    (hval : coeff jst (fun t => H1 ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
      (κ0 : Matrix (Fin 4) (Fin 4) ℝ))) ≠ 0)
    (hwin : ∀ j : ℤ, |j| + 1 < ((r + m : ℕ) : ℤ) → ∀ κ ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 1 j (frobMap hJ2 (frobMap hJ1 w0)) κ = 0)
    (hpar : Even (((r + m : ℕ) : ℤ) - ((par h41 e2 : ℕ) : ℤ)))
    {jf : ℤ}
    (hfin : ∀ g : ℂ, g ≠ 0 → coeff jf (fun θ => 2 * (Real.pi : ℂ) * g *
      ((yZ h41 u ^ r * wp u u' ^ m) (blockRotation 4 rb θ : Matrix (Fin 4) (Fin 4) ℝ) -
        (-1) ^ ((e2 2).val + (e2 3).val) * (yZ h41 u ^ r * wp u u' ^ m)
          (fl 3 * (fl 2 * (blockRotation 4 rb θ : Matrix (Fin 4) (Fin 4) ℝ))))) ≠ 0) :
    coeff jf (fun θ => ∑ᶠ j : ℤ, ((Int.sign j : ℤ) : ℂ) *
      blockFourierCoefficient 4 1 j (frobMap hJ2 (frobMap hJ1 w0)) (blockRotation 4 rb θ)) ≠ 0 := by
  obtain ⟨H2, hH2, hw1⟩ := frobMap_eq_on hJ1 (hasExpTop_Sm1 u u' r m) w0 hH1 hw0
  obtain ⟨H3, hH3, hw⟩ := frobMap_eq_on hJ2 hS2 (frobMap hJ1 w0) hH2 hw1
  obtain ⟨P, hP, -, hPT⟩ := hasExpTop_Sm1 u u' r m H3 hH3
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hPT
  -- the top mode
  have htop : ∀ κ ∈ SOset 4, blockFourierCoefficient 4 1 ((r + m : ℕ) : ℤ)
      (frobMap hJ2 (frobMap hJ1 w0)) κ = 2 * (Real.pi : ℂ) *
        (g * (yZ h41 u ^ r * wp u u' ^ m) (κ : Matrix (Fin 4) (Fin 4) ℝ)) := by
    intro κ hκ
    rw [blockFourierCoefficient_eq_of_expansion hP hw hκ, ite_eq_left ⟨by omega, by omega⟩]
    have h2 : (((r + m : ℕ) : ℤ) + ((r + m : ℕ) : ℤ)).toNat = 2 * (r + m) := by omega
    rw [h2, ← hg]
    rfl
  -- the bottom mode
  have hbot : ∀ κ ∈ SOset 4, blockFourierCoefficient 4 1 (-((r + m : ℕ) : ℤ))
      (frobMap hJ2 (frobMap hJ1 w0)) κ = (-1) ^ ((e2 2).val + (e2 3).val) *
        (2 * (Real.pi : ℂ) * (g * (yZ h41 u ^ r * wp u u' ^ m)
          (fl 3 * (fl 2 * (κ : Matrix (Fin 4) (Fin 4) ℝ))))) := by
    intro κ hκ
    rw [blockFourierCoefficient_neg_one, htop _ (sign_mem_SOset hκ), sign_val]
  -- the other modes
  have hother : ∀ κ ∈ SOset 4, ∀ j : ℤ, j ≠ ((r + m : ℕ) : ℤ) → j ≠ -((r + m : ℕ) : ℤ) →
      blockFourierCoefficient 4 1 j (frobMap hJ2 (frobMap hJ1 w0)) κ = 0 :=
    fun κ hκ j h1 h2 => blockFourierCoefficient_one_eq_zero _ hP hw hwin hpar h1 h2 hκ
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  -- `g ≠ 0`
  have hg0 : g ≠ 0 := by
    intro hg0
    have hw0' : ∀ κ ∈ SOset 4,
        ((frobMap hJ2 (frobMap hJ1 w0) : KF 4 _) : Langlands.GeneralLinear 4 ℝ → ℂ) κ = 0 := by
      intro κ hκ
      refine eq_zero_of_modes hP (fun t => hw _ (rot_mul_mem_SOset hκ 1 t)) (fun j => ?_)
      by_cases h1 : j = ((r + m : ℕ) : ℤ)
      · rw [h1, htop κ hκ, hg0]
        ring
      by_cases h2 : j = -((r + m : ℕ) : ℤ)
      · rw [h2, hbot κ hκ, hg0]
        ring
      exact hother κ hκ j h1 h2
    obtain ⟨P', hP', -, -⟩ := hS2 H2 hH2
    have hw1' : ∀ κ ∈ SOset 4,
        ((frobMap hJ1 w0 : KF 4 _) : Langlands.GeneralLinear 4 ℝ → ℂ) κ = 0 := by
      intro κ hκ
      refine eq_zero_of_modes hP' (fun t => hw1 _ (rot_mul_mem_SOset hκ b2 t)) (fun j => ?_)
      exact blockFourierCoefficient_eq_zero_of_frobMap hb2 hJ2 _ hw0' (hμ2 j) hκ
    apply hval
    have h := blockFourierCoefficient_eq_zero_of_frobMap h41 hJ1 w0 hw1' hμ1 hκ0
    rw [blockFourierCoefficient_eq_coeff] at h
    have e : (fun θ => (w0 : Langlands.GeneralLinear 4 ℝ → ℂ) (blockRotation 4 1 θ * κ0)) =
        fun t => H1 ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
          (κ0 : Matrix (Fin 4) (Fin 4) ℝ)) :=
      funext fun t => hw0 _ (rot_mul_mem_SOset hκ0 1 t)
    rw [← e]
    exact h
  -- the final function
  have e : (fun θ => ∑ᶠ j : ℤ, ((Int.sign j : ℤ) : ℂ) *
      blockFourierCoefficient 4 1 j (frobMap hJ2 (frobMap hJ1 w0)) (blockRotation 4 rb θ)) =
      fun θ => 2 * (Real.pi : ℂ) * g *
        ((yZ h41 u ^ r * wp u u' ^ m) (blockRotation 4 rb θ : Matrix (Fin 4) (Fin 4) ℝ) -
          (-1) ^ ((e2 2).val + (e2 3).val) * (yZ h41 u ^ r * wp u u' ^ m)
            (fl 3 * (fl 2 * (blockRotation 4 rb θ : Matrix (Fin 4) (Fin 4) ℝ)))) := by
    funext θ
    have hκ := blockRotation_mem_SOset (n := 4) rb θ
    rw [finsum_sign_two (by omega) _ (hother _ hκ), htop _ hκ, hbot _ hκ]
    ring
  rw [e]
  exact hfin g hg0

end Main

/-! ## Test functions -/

section TestFunctions

variable {b : ℕ}

/-- `G₊ = y^r ν₊^m` for the coordinate `y = y_b + i y_{b+1}` of the column `X u`. -/
def Gp (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) : MF 4 := yZ hb u ^ r * nup u u' ^ m

/-- `G₋ = ȳ^r ν₋^m`. -/
def Gm (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) : MF 4 := yZb hb u ^ r * num u u' ^ m

/-- `F = G₊ + G₋`. -/
def Fp (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) : MF 4 := Gp hb u u' r m + Gm hb u u' r m

theorem Gp_apply (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Gp hb u u' r m X = yZ hb u X ^ r * nup u u' X ^ m :=
  rfl

theorem Gm_apply (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Gm hb u u' r m X = yZb hb u X ^ r * num u u' X ^ m :=
  rfl

theorem Fp_apply (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Fp hb u u' r m X = yZ hb u X ^ r * nup u u' X ^ m + yZb hb u X ^ r * num u u' X ^ m :=
  rfl

theorem Gp_mem_Sm (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) :
    Gp hb u u' r m ∈ Sm u u' r m :=
  Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (yZ_mem_Ly hb u) r)
    (Submodule.pow_mem_pow _ (nup_mem_Lw u u') m)

theorem Gm_mem_Sm (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) :
    Gm hb u u' r m ∈ Sm u u' r m :=
  Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (yZb_mem_Ly hb u) r)
    (Submodule.pow_mem_pow _ (num_mem_Lw u u') m)

theorem yZ_mem_PF (hb : b + 1 < 4) (u : Fin 4 → ℂ) : yZ hb u ∈ PF 4 := by
  have e : yZ hb u = colv u (ia hb) + Complex.I • colv u (ib hb) := by
    funext X
    simp [yZ]
  rw [e]
  exact Subalgebra.add_mem _ (colv_mem_PF u _) (Subalgebra.smul_mem _ (colv_mem_PF u _) _)

theorem yZb_mem_PF (hb : b + 1 < 4) (u : Fin 4 → ℂ) : yZb hb u ∈ PF 4 := by
  have e : yZb hb u = colv u (ia hb) + (-Complex.I) • colv u (ib hb) := by
    funext X
    simp [yZb, sub_eq_add_neg]
  rw [e]
  exact Subalgebra.add_mem _ (colv_mem_PF u _) (Subalgebra.smul_mem _ (colv_mem_PF u _) _)

theorem nup_mem_PF (u u' : Fin 4 → ℂ) : nup u u' ∈ PF 4 := by
  have e : nup u u' = w2 u u' + Complex.I • w3 u u' := by
    funext X
    simp [nup]
  rw [e]
  exact Subalgebra.add_mem _ (w2_mem_PF u u') (Subalgebra.smul_mem _ (w3_mem_PF u u') _)

theorem num_mem_PF (u u' : Fin 4 → ℂ) : num u u' ∈ PF 4 := by
  have e : num u u' = w2 u u' + (-Complex.I) • w3 u u' := by
    funext X
    simp [num, sub_eq_add_neg]
  rw [e]
  exact Subalgebra.add_mem _ (w2_mem_PF u u') (Subalgebra.smul_mem _ (w3_mem_PF u u') _)

theorem Fp_mem_PF (hb : b + 1 < 4) (u u' : Fin 4 → ℂ) (r m : ℕ) : Fp hb u u' r m ∈ PF 4 :=
  Subalgebra.add_mem _
    (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (yZ_mem_PF hb u) r)
      (Subalgebra.pow_mem _ (nup_mem_PF u u') m))
    (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (yZb_mem_PF hb u) r)
      (Subalgebra.pow_mem _ (num_mem_PF u u') m))

/-! ### Double flips -/

theorem pl_fl (u u' : Fin 4 → ℂ) (a i j : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    pl u u' i j (fl a * X) =
      ((if i = a then -1 else 1) * (if j = a then -1 else 1)) * pl u u' i j X := by
  simp only [pl, colv_fl]
  ring

theorem w_fl30 (u u' : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    w2 u u' (fl 3 * (fl 0 * X)) = -w2 u u' X ∧ w3 u u' (fl 3 * (fl 0 * X)) = w3 u u' X := by
  simp only [w2, w3, pl_fl]
  constructor
  · norm_num
    ring
  · norm_num

theorem w_fl31 (u u' : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    w2 u u' (fl 3 * (fl 1 * X)) = w2 u u' X ∧ w3 u u' (fl 3 * (fl 1 * X)) = -w3 u u' X := by
  simp only [w2, w3, pl_fl]
  constructor
  · norm_num
  · norm_num
    ring

theorem w_fl32 (u u' : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    w1 u u' (fl 3 * (fl 2 * X)) = w1 u u' X ∧ w2 u u' (fl 3 * (fl 2 * X)) = -w2 u u' X ∧
      w3 u u' (fl 3 * (fl 2 * X)) = -w3 u u' X := by
  simp only [w1, w2, w3, pl_fl]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num <;> ring

theorem nu_fl30 (u u' : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    nup u u' (fl 3 * (fl 0 * X)) = -num u u' X ∧ num u u' (fl 3 * (fl 0 * X)) = -nup u u' X := by
  obtain ⟨h2, h3⟩ := w_fl30 u u' X
  simp only [nup, num, h2, h3]
  constructor <;> ring

theorem nu_fl31 (u u' : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    nup u u' (fl 3 * (fl 1 * X)) = num u u' X ∧ num u u' (fl 3 * (fl 1 * X)) = nup u u' X := by
  obtain ⟨h2, h3⟩ := w_fl31 u u' X
  simp only [nup, num, h2, h3]
  constructor <;> ring

theorem nu_fl32 (u u' : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    nup u u' (fl 3 * (fl 2 * X)) = -nup u u' X ∧ num u u' (fl 3 * (fl 2 * X)) = -num u u' X := by
  obtain ⟨-, h2, h3⟩ := w_fl32 u u' X
  simp only [nup, num, h2, h3]
  constructor <;> ring

theorem colv_fl3fl (u : Fin 4 → ℂ) (i a : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    colv u i (fl 3 * (fl a * X)) =
      ((if i = 3 then -1 else 1) * (if i = a then -1 else 1)) * colv u i X := by
  rw [colv_fl, colv_fl]
  ring

theorem yZ0_apply (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h40 u X = colv u 0 X + Complex.I * colv u 1 X :=
  rfl

theorem yZb0_apply (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZb h40 u X = colv u 0 X - Complex.I * colv u 1 X :=
  rfl

theorem yZ1_apply (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h41 u X = colv u 1 X + Complex.I * colv u 2 X :=
  rfl

theorem yZ2_apply (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h42 u X = colv u 2 X + Complex.I * colv u 3 X :=
  rfl

theorem yZb2_apply (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZb h42 u X = colv u 2 X - Complex.I * colv u 3 X :=
  rfl

theorem wp_apply (u u' : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    wp u u' X = w1 u u' X + Complex.I * w2 u u' X :=
  rfl

theorem yZ0_fl30 (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h40 u (fl 3 * (fl 0 * X)) = -yZb h40 u X ∧ yZb h40 u (fl 3 * (fl 0 * X)) = -yZ h40 u X := by
  simp only [yZ0_apply, yZb0_apply, colv_fl3fl]
  norm_num
  constructor <;> ring

theorem yZ0_fl31 (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h40 u (fl 3 * (fl 1 * X)) = yZb h40 u X ∧ yZb h40 u (fl 3 * (fl 1 * X)) = yZ h40 u X := by
  simp only [yZ0_apply, yZb0_apply, colv_fl3fl]
  norm_num
  ring

theorem yZ0_fl32 (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h40 u (fl 3 * (fl 2 * X)) = yZ h40 u X ∧ yZb h40 u (fl 3 * (fl 2 * X)) = yZb h40 u X := by
  simp only [yZ0_apply, yZb0_apply, colv_fl3fl]
  norm_num

theorem yZ2_fl30 (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h42 u (fl 3 * (fl 0 * X)) = yZb h42 u X ∧ yZb h42 u (fl 3 * (fl 0 * X)) = yZ h42 u X := by
  simp only [yZ2_apply, yZb2_apply, colv_fl3fl]
  norm_num
  ring

theorem yZ2_fl31 (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h42 u (fl 3 * (fl 1 * X)) = yZb h42 u X ∧ yZb h42 u (fl 3 * (fl 1 * X)) = yZ h42 u X := by
  simp only [yZ2_apply, yZb2_apply, colv_fl3fl]
  norm_num
  ring

theorem yZ2_fl32 (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h42 u (fl 3 * (fl 2 * X)) = -yZ h42 u X ∧ yZb h42 u (fl 3 * (fl 2 * X)) = -yZb h42 u X := by
  simp only [yZ2_apply, yZb2_apply, colv_fl3fl]
  norm_num
  constructor <;> ring

/-! ### Signs of the test functions -/

/-- The column at the block `0`: signs `(r + m, 0, m, 0)`. -/
theorem isSignEq_Fp0 (u u' : Fin 4 → ℂ) (r m : ℕ) :
    IsSignEq ![r + m, 0, m, 0] (detExt (Fp h40 u u' r m)) := by
  refine isSignEq_detExt (fun i hi X => ?_) (by simp)
  fin_cases i
  · show Fp h40 u u' r m (fl 3 * (fl 0 * X)) = (-1) ^ (r + m) * Fp h40 u u' r m X
    obtain ⟨h1, h2⟩ := nu_fl30 u u' X
    obtain ⟨h3, h4⟩ := yZ0_fl30 u X
    rw [Fp_apply, Fp_apply, h1, h2, h3, h4, neg_pow (yZb h40 u X), neg_pow (num u u' X),
      neg_pow (yZ h40 u X), neg_pow (nup u u' X), pow_add]
    ring
  · show Fp h40 u u' r m (fl 3 * (fl 1 * X)) = (-1) ^ 0 * Fp h40 u u' r m X
    obtain ⟨h1, h2⟩ := nu_fl31 u u' X
    obtain ⟨h3, h4⟩ := yZ0_fl31 u X
    rw [Fp_apply, Fp_apply, h1, h2, h3, h4]
    ring
  · show Fp h40 u u' r m (fl 3 * (fl 2 * X)) = (-1) ^ m * Fp h40 u u' r m X
    obtain ⟨h1, h2⟩ := nu_fl32 u u' X
    obtain ⟨h3, h4⟩ := yZ0_fl32 u X
    rw [Fp_apply, Fp_apply, h1, h2, h3, h4, neg_pow (nup u u' X), neg_pow (num u u' X)]
    ring
  · exact absurd rfl hi

/-- The column at the block `2`: signs `(m, 0, r + m, 0)`. -/
theorem isSignEq_Fp2 (u u' : Fin 4 → ℂ) (r m : ℕ) :
    IsSignEq ![m, 0, r + m, 0] (detExt (Fp h42 u u' r m)) := by
  refine isSignEq_detExt (fun i hi X => ?_) (by simp)
  fin_cases i
  · show Fp h42 u u' r m (fl 3 * (fl 0 * X)) = (-1) ^ m * Fp h42 u u' r m X
    obtain ⟨h1, h2⟩ := nu_fl30 u u' X
    obtain ⟨h3, h4⟩ := yZ2_fl30 u X
    rw [Fp_apply, Fp_apply, h1, h2, h3, h4, neg_pow (num u u' X), neg_pow (nup u u' X)]
    ring
  · show Fp h42 u u' r m (fl 3 * (fl 1 * X)) = (-1) ^ 0 * Fp h42 u u' r m X
    obtain ⟨h1, h2⟩ := nu_fl31 u u' X
    obtain ⟨h3, h4⟩ := yZ2_fl31 u X
    rw [Fp_apply, Fp_apply, h1, h2, h3, h4]
    ring
  · show Fp h42 u u' r m (fl 3 * (fl 2 * X)) = (-1) ^ (r + m) * Fp h42 u u' r m X
    obtain ⟨h1, h2⟩ := nu_fl32 u u' X
    obtain ⟨h3, h4⟩ := yZ2_fl32 u X
    rw [Fp_apply, Fp_apply, h1, h2, h3, h4, neg_pow (yZ h42 u X), neg_pow (nup u u' X),
      neg_pow (yZb h42 u X), neg_pow (num u u' X), pow_add]
    ring
  · exact absurd rfl hi

/-! ### Two modes -/

theorem expMode_one_pow_mul (φ : ℝ) (r m : ℕ) :
    expMode 1 φ ^ r * expMode 1 φ ^ m = expMode ((r + m : ℕ) : ℤ) φ := by
  rw [← pow_add, expMode_one_pow]

theorem expMode_neg_one_pow_mul (φ : ℝ) (r m : ℕ) :
    expMode (-1) φ ^ r * expMode (-1) φ ^ m = expMode (-((r + m : ℕ) : ℤ)) φ := by
  rw [← pow_add, expMode_pow]
  congr 1
  ring

theorem Fp0_rot0 (u u' : Fin 4 → ℂ) (r m : ℕ) (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Fp h40 u u' r m ((blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode ((r + m : ℕ) : ℤ) φ * Gp h40 u u' r m X +
        expMode (-((r + m : ℕ) : ℤ)) φ * Gm h40 u u' r m X := by
  rw [Fp_apply, Gp_apply, Gm_apply, yZ_rot, yZb_rot, nup_rot0, num_rot0, mul_pow, mul_pow,
    mul_pow, mul_pow, ← expMode_one_pow_mul, ← expMode_neg_one_pow_mul]
  ring

theorem Fp0_rot2 (u u' : Fin 4 → ℂ) (r m : ℕ) (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Fp h40 u u' r m ((blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode (m : ℤ) φ * Gp h40 u u' r m X + expMode (-(m : ℤ)) φ * Gm h40 u u' r m X := by
  rw [Fp_apply, Gp_apply, Gm_apply, yZ_rot_of_disjoint h40 h42 (Or.inl (by norm_num)),
    yZb_rot_of_disjoint h40 h42 (Or.inl (by norm_num)), nup_rot2, num_rot2, mul_pow, mul_pow,
    expMode_one_pow, expMode_pow]
  ring_nf

theorem Fp2_rot0 (u u' : Fin 4 → ℂ) (r m : ℕ) (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Fp h42 u u' r m ((blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode (m : ℤ) φ * Gp h42 u u' r m X + expMode (-(m : ℤ)) φ * Gm h42 u u' r m X := by
  rw [Fp_apply, Gp_apply, Gm_apply, yZ_rot_of_disjoint h42 h40 (Or.inr (by norm_num)),
    yZb_rot_of_disjoint h42 h40 (Or.inr (by norm_num)), nup_rot0, num_rot0, mul_pow, mul_pow,
    expMode_one_pow, expMode_pow]
  ring_nf

theorem Fp2_rot2 (u u' : Fin 4 → ℂ) (r m : ℕ) (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Fp h42 u u' r m ((blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode ((r + m : ℕ) : ℤ) φ * Gp h42 u u' r m X +
        expMode (-((r + m : ℕ) : ℤ)) φ * Gm h42 u u' r m X := by
  rw [Fp_apply, Gp_apply, Gm_apply, yZ_rot, yZb_rot, nup_rot2, num_rot2, mul_pow, mul_pow,
    mul_pow, mul_pow, ← expMode_one_pow_mul, ← expMode_neg_one_pow_mul]
  ring

end TestFunctions

/-! ## Test vectors in the standard module of two induction blocks -/

section TestVector

/-- **Test vectors.** A function `G ∈ PF` whose extension by the determinant has the signs of the
positions of `[d, e]`, with two modes `±N₀` at the block `0` and `±N₂` at the block `2` beyond the
weights, is the restriction to `O(4)` of an `O(4)`-finite vector of the standard module. -/
theorem exists_test_of {d e : ComplexCharacterData} {G A0 B0 A2 B2 : MF 4} (hG : G ∈ PF 4)
    {Q : Fin 4 → ℕ} (hQ : IsSignEq Q (detExt G))
    (hQ0 : (-1 : ℂ) ^ Q 0 = (-1) ^ (d.weight.natAbs + 1)) (hQ1 : (-1 : ℂ) ^ Q 1 = 1)
    (hQ2 : (-1 : ℂ) ^ Q 2 = (-1) ^ (e.weight.natAbs + 1)) (hQ3 : (-1 : ℂ) ^ Q 3 = 1)
    {N0 N2 : ℤ}
    (h0 : ∀ (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ),
      G ((blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        expMode N0 φ * A0 X + expMode (-N0) φ * B0 X)
    (hN0 : (d.weight.natAbs : ℤ) ≤ |N0|)
    (h2 : ∀ (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ),
      G ((blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        expMode N2 φ * A2 X + expMode (-N2) φ * B2 X)
    (hN2 : (e.weight.natAbs : ℤ) ≤ |N2|) :
    ∃ v : KF 4 [RealBlock.induced d, RealBlock.induced e], ∀ g ∈ unitaryCompact ℝ 4,
      (v : Langlands.GeneralLinear 4 ℝ → ℂ) g = detExt G (g : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hdet := detExt_mem_PF hG
  refine exists_KF (n := 4) (ds := [RealBlock.induced d, RealBlock.induced e]) rfl hdet.1 hdet.2
    hQ (fun i => ?_) ?_
  · fin_cases i
    · show (-1 : ℂ) ^ Q 0 = realInducedFirstCharacter d (-1)
      rw [hQ0, realInducedFirstCharacter_neg_one]
    · show (-1 : ℂ) ^ Q 1 = realInducedSecondCharacter d (-1)
      rw [hQ1, realInducedSecondCharacter_neg_one]
    · show (-1 : ℂ) ^ Q 2 = realInducedFirstCharacter e (-1)
      rw [hQ2, realInducedFirstCharacter_neg_one]
    · show (-1 : ℂ) ^ Q 3 = realInducedSecondCharacter e (-1)
      rw [hQ3, realInducedSecondCharacter_neg_one]
  · intro p d' hd j hj κ hκ
    rcases p with _ | _ | _ | _ | p
    · simp only [realInducedBlockAt, Option.some.injEq] at hd
      subst hd
      rw [Int.abs_eq_natAbs d.weight] at hj
      exact coeff_detExt_eq_zero (Or.inl rfl) h0 (by omega) hκ
    · simp [realInducedBlockAt] at hd
    · simp only [realInducedBlockAt, Option.some.injEq] at hd
      subst hd
      rw [Int.abs_eq_natAbs e.weight] at hj
      exact coeff_detExt_eq_zero (Or.inr rfl) h2 (by omega) hκ
    · simp [realInducedBlockAt] at hd
    · simp [realInducedBlockAt] at hd

/-- On `SO(4)` the test vector has the two modes of `G` along the block `b`. -/
theorem test_two_mode {ds : List RealBlock} {G A B : MF 4} {v : KF 4 ds}
    (hv : ∀ g ∈ unitaryCompact ℝ 4,
      (v : Langlands.GeneralLinear 4 ℝ → ℂ) g = detExt G (g : Matrix (Fin 4) (Fin 4) ℝ))
    {b : ℕ} {N : ℤ}
    (hG : ∀ (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ),
      G ((blockRotation 4 b φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        expMode N φ * A X + expMode (-N) φ * B X) :
    ∀ κ ∈ SOset 4, ∀ φ : ℝ, (v : Langlands.GeneralLinear 4 ℝ → ℂ) (blockRotation 4 b φ * κ) =
      expMode N φ * A (κ : Matrix (Fin 4) (Fin 4) ℝ) +
        expMode (-N) φ * B (κ : Matrix (Fin 4) (Fin 4) ℝ) := by
  intro κ hκ φ
  have hm := rot_mul_mem_SOset hκ b φ
  rw [hv _ hm.1, detExt_of_det_one hm.2]
  exact hG φ _

end TestVector

end RealInterlacedJacquet

end Langlands.Archimedean
