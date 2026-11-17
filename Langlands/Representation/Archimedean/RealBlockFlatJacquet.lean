import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Representation.Archimedean.RealInterlacedLinkedJacquetStatement
import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Langlands.Representation.Archimedean.JacquetKernel
import Langlands.Representation.Archimedean.RealInductionStagesFourier

/-!
# Flat block multipliers and linked pairs with an induction block

A multiplier `μ` that is flat at an induction block gives a real Jacquet functional `ℓ_μ` with
the exponents of the list. Its Frobenius map lands in a principal series, where the binomial
functional at a linked pair of positions gives `RealLinkedJacquetFunctionalExists`.
Nonvanishing is checked on explicit test functions on `O(n)`. This proves the pair kinds IC, CI and
the separated case of II of `RealLinkedJacquetPairReduction`, and reduces II to
`RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealBlockFlatJacquet

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealBlockDerivative RealCharacterCrossing InductionStages

variable {n : ℕ}

/-! ## Flat multipliers -/

/-- The algebra of the tridiagonal formula for a flat multiplier: if `c` has bounded support
and `μ_{j ± 2} (δ ± j) = μ_j (δ ± j)` wherever `c_j ≠ 0`, the multiplier sum of the tridiagonal
combination is `S` times the multiplier sum of `c`. -/
theorem finsum_flat {μ c : ℤ → ℂ} {δ : ℂ} (D : ℕ)
    (hc : ∀ j : ℤ, (D : ℤ) < |j| → c j = 0)
    (hflat : ∀ j : ℤ, c j ≠ 0 →
      μ (j + 2) * (δ + j) = μ j * (δ + j) ∧ μ (j - 2) * (δ - j) = μ j * (δ - j))
    (S x y v : ℂ) :
    ∑ᶠ j : ℤ, μ j * ((S - δ * (x - y) / 2 - Complex.I * v * j / 2) * c j +
        (x - y + Complex.I * v) / 4 * (δ + j - 2) * c (j - 2) +
        (x - y - Complex.I * v) / 4 * (δ - j - 2) * c (j + 2)) =
      S * ∑ᶠ j : ℤ, μ j * c j := by
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
  by_cases hj : c j = 0
  · simp [hj]
  · obtain ⟨r1, r2⟩ := hflat j hj
    linear_combination c j * (x - y + Complex.I * v) / 4 * r1 +
      c j * (x - y - Complex.I * v) / 4 * r2

section Standard

variable {ds : List RealBlock} {p : ℕ} {μ : ℤ → ℂ}

/-- **Right derivatives for a flat multiplier.** For an upper triangular `A`,
`Σᶠ μ_j Φ_j(R_A f)(1) = (Σ_i α_i A_ii) Σᶠ μ_j Φ_j(f)(1)` with `α_i = τ_i + (n - 1)/2 - i`,
provided `μ` is flat for `δ = α_p - α_{p+1}` at the modes of the functions of the module. -/
theorem finsum_rightDerivative_flat (hp : p + 1 < n) {τ : Fin n → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    (hflat : ∀ (f : KF n ds) (j : ℤ), blockFourierCoefficient n p j f 1 ≠ 0 →
      μ (j + 2) * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) + j) =
        μ j * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) + j) ∧
      μ (j - 2) * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) - j) =
        μ j * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) - j))
    (f : KF n ds) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsUpperTriangular) :
    ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j (rightDerivative (matrixModel ℝ n) A f) 1 =
      (∑ i, (τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) * (A i i : ℂ)) *
        ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j f 1 := by
  have hα := isExpEquivariant_of_mem_principalSeries hτ f.2.1.1
  have hsm := contMDiff_of_mem_realStandardModule f.2.1
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  simp_rw [blockFourierCoefficient_rightDerivative hp hsm hα hA (X := A) 1 (by simp)]
  exact finsum_flat D (fun j hj => hD j hj 1 (one_mem _)) (hflat f) _ _ _ _

/-- **A flat multiplier gives a real Jacquet functional with the exponents of `ds`.** If `μ`
is flat for `δ = α_p - α_{p+1}` at the modes of the functions of the module and symmetric for
`σ`, then `ℓ_μ` is a real Jacquet functional with the exponents `α_i = τ_i + (n - 1)/2 - i` and
signs `e` with `(-1)^{e_i} = χ_i(-1)` off the block and `(-1)^{e_i} = χ_i(-1) σ` on it. -/
theorem isRealJacquetFunctional_blockJacquet_flat (hp : p + 1 < n) {τ : Fin n → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1))
    (hflat : ∀ (f : KF n ds) (j : ℤ), blockFourierCoefficient n p j f 1 ≠ 0 →
      μ (j + 2) * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) + j) =
        μ j * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) + j) ∧
      μ (j - 2) * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) - j) =
        μ j * (((τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
          (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ))) - j))
    {σ : ℂ} (hsym : IsSymmetric ε σ μ) {e : Fin n → Fin 2}
    (he_off : ∀ i : Fin n, i ≠ ia hp → i ≠ ib hp →
      (-1 : ℂ) ^ (e i).val = realPositionCharacter ds i (-1))
    (he_p : (-1 : ℂ) ^ (e (ia hp)).val = realPositionCharacter ds p (-1) * σ)
    (he_q : (-1 : ℂ) ^ (e (ib hp)).val = realPositionCharacter ds (p + 1) (-1) * σ) :
    IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
      (blockJacquet n ds p μ) (fun i => τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) e := by
  refine ⟨fun X hX f => ?_, fun i f => ⟨?_, blockJacquet_hsign hp hpar hsym he_off he_p he_q i f⟩⟩
  · have hU : X.IsUpperTriangular := fun i k hik => hX i k (le_of_lt hik)
    have hdiag : ∀ i, X i i = 0 := fun i => hX i i le_rfl
    rw [blockJacquet_apply, realStandardLie_one_tmul_apply_coe,
      finsum_rightDerivative_flat hp hτ hflat f hU]
    simp [hdiag]
  · have hU : (Matrix.single i i (1 : ℝ)).IsUpperTriangular := fun k l hkl => by
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hkl
    rw [blockJacquet_apply, blockJacquet_apply, realStandardLie_one_tmul_apply_coe,
      finsum_rightDerivative_flat hp hτ hflat f hU]
    have hsum : ∑ k, (τ k + ((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ)) *
        ((Matrix.single i i (1 : ℝ) k k : ℝ) : ℂ) = τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hk h.1.symm)]
        simp
      · simp
    rw [hsum]
    ring

end Standard

/-! ## Composites with an intertwiner -/

section Composite

variable {ds ds' : List RealBlock}

/-- **Nonvanishing through an intertwiner.** If `B` commutes with `O(n)` and some `B v` has a
nonzero block Fourier coefficient `Φ_j(B v)(1)` with `μ_j ≠ 0`, then `ℓ_μ ∘ B ≠ 0`: otherwise the
Frobenius function of `ℓ_μ` at `B v` vanishes on `O(n)`, and so does its coefficient
`μ_j Φ_j(B v)(1)`. -/
theorem blockJacquet_comp_ne_zero {r : ℕ} (hr : r + 1 < n) {μ : ℤ → ℂ} {e : Fin n → Fin 2}
    (hsign : ∀ (i : Fin n) (w : KF n ds'),
      blockJacquet n ds' r μ (realStandardRep n ds' (signReflection n i) w) =
        (-1) ^ (e i).val * blockJacquet n ds' r μ w)
    (B : KF n ds →ₗ[ℂ] KF n ds')
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n ds' κ (B v))
    {j : ℤ} (hμ : μ j ≠ 0) (v : KF n ds) (hv : blockFourierCoefficient n r j (B v) 1 ≠ 0) :
    blockJacquet n ds' r μ ∘ₗ B ≠ 0 := by
  intro h0
  have hF : ∀ θ : ℝ, RealJacquetFrobenius.frobFun (realStandardRep n ds')
      (blockJacquet n ds' r μ) 0 e (B v) (blockRotation n r θ * 1) = 0 := by
    intro θ
    have hk := blockRotation_mem_unitaryCompact n r θ
    rw [mul_one, RealJacquetFrobenius.frobFun_eq hsign (b := 1)
      (k := (blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ)) Matrix.blockTriangular_one hk
      (one_mul _).symm (B v), diagChar_one, one_mul, ← hrep]
    exact LinearMap.congr_fun h0 _
  have h := blockFourierCoefficient_frobFun (a := 0) hr hsign (B v)
    (one_mem (unitaryCompact ℝ n)) j
  have h1 : blockFourierCoefficient n r j (RealJacquetFrobenius.frobFun (realStandardRep n ds')
      (blockJacquet n ds' r μ) 0 e (B v)) 1 = 0 := by
    unfold blockFourierCoefficient
    simp_rw [hF, zero_mul]
    simp
  rw [h1] at h
  exact mul_ne_zero hμ hv h.symm

/-- The `k`-th power of `π(Y)` commutes with an intertwiner. -/
theorem map_pow_lie (B : KF n ds →ₗ[ℂ] KF n ds')
    (hlie : ∀ Y v, B (realStandardLie n ds Y v) = realStandardLie n ds' Y (B v))
    (m : ℕ) (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (w : KF n ds) :
    B ((realStandardLie n ds Y ^ m) w) = (realStandardLie n ds' Y ^ m) (B w) := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, hlie, pow_succ, Module.End.mul_apply]

/-- **A linked adjacent pair after an intertwiner.** Let `B` be a `(𝔤, K)`-intertwiner from
the `O(n)`-finite functions of the standard module of `ds` to those of the principal series of
the characters `sgn^{e_i} |·|^{τ_i}`. If `τ_r - τ_{r+1} = k > 0` with `k + e_r + e_{r+1}` odd
and some `B v` has a nonzero block Fourier coefficient at `r` in the parity class of the
block, the binomial functional at `r` composed with `B` is as in
`RealLinkedJacquetFunctionalExists`. -/
theorem exists_of_comp {τ : Fin n → ℂ} {e : Fin n → Fin 2} (B : KF n ds →ₗ[ℂ] KF n (PL τ e))
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n (PL τ e) κ (B v))
    (hlie : ∀ Y v, B (realStandardLie n ds Y v) = realStandardLie n (PL τ e) Y (B v))
    {r : ℕ} (hr : r + 1 < n) {k : ℕ} (hk : 0 < k) (hτ : τ (ia hr) - τ (ib hr) = k)
    (hodd : Odd (k + (e (ia hr)).val + (e (ib hr)).val))
    (v : KF n ds) (hv : blockFourierCoefficient n r (par hr e) (B v) 1 ≠ 0) :
    RealLinkedJacquetFunctionalExists n ds := by
  set ε : ℤ := ((par hr e : ℕ) : ℤ) with hεdef
  have hε : ε = 0 ∨ ε = 1 := par_cases hr e
  have hpar : Even ((k : ℤ) - 1 - ε) := by
    rw [hεdef, Int.even_iff]
    unfold par
    obtain ⟨m, hm⟩ := hodd
    omega
  set μ := binomialMultiplier k ε with hμdef
  have hrec : IsRecurrent (τ (ia hr) - τ (ib hr) + 1) (par hr e) μ := by
    rw [hτ]
    exact isRecurrent_binomialMultiplier hk hε hpar
  have hsym : IsSymmetric (par hr e) ((-1) ^ par hr e) μ :=
    isSymmetric_binomialMultiplier k hε
  have hJ := isJacquet_cross hr τ e hrec hsym
  have hsign : ∀ (i : Fin n) (w : KF n (PL τ e)),
      blockJacquet n (PL τ e) r μ (realStandardRep n (PL τ e) (signReflection n i) w) =
        (-1) ^ ((e ∘ sw hr) i).val * blockJacquet n (PL τ e) r μ w := fun i w => (hJ.2 i w).2
  have ha : crossExp hr τ (ia hr) - crossExp hr τ (ib hr) = 1 - (k : ℂ) := by
    rw [crossExp_sub]
    linear_combination -hτ
  have hwin : ∀ (j : ℤ) (f : KF n (PL τ e)), μ j * blockFourierCoefficient n r j f 1 ≠ 0 →
      |j| < k ∧ Even ((k : ℤ) - 1 - j) := by
    intro j f h
    have hj : Even (j - ε) := by
      by_contra hj
      exact h (by rw [blockFourierCoefficient_eq_zero_of_not_even hr (PL_parity hr τ e) f hj 1,
        mul_zero])
    refine ⟨(binomialMultiplier_ne_zero_iff hk hε hpar hj).mp (left_ne_zero_of_mul h), ?_⟩
    rw [Int.even_iff] at hj hpar ⊢
    omega
  have hpow := blockJacquet_pow_eq_zero hr hJ hk ha hwin
  have hμ0 : μ ε ≠ 0 := by
    refine (binomialMultiplier_ne_zero_iff (k := ε) hk hε hpar
      (by rw [sub_self]; exact Even.zero)).mpr ?_
    rw [Int.even_iff] at hpar
    rw [abs_lt]
    omega
  refine ⟨blockJacquet n (PL τ e) r μ ∘ₗ B, crossExp hr τ, e ∘ sw hr, r, k, hr,
    blockJacquet_comp_ne_zero hr hsign B hrep hμ0 v hv,
    ⟨fun X hX w => ?_, fun j w => ⟨?_, ?_⟩⟩, ha, fun w => ?_⟩
  · simp only [LinearMap.comp_apply, hlie]
    exact hJ.1 X hX (B w)
  · simp only [LinearMap.comp_apply, hlie]
    exact (hJ.2 j (B w)).1
  · simp only [LinearMap.comp_apply, hrep]
    exact (hJ.2 j (B w)).2
  · rw [LinearMap.comp_apply, map_pow_lie B hlie]
    exact hpow (B w)

end Composite

/-! ## The flat engine -/

section Engine

variable {ds : List RealBlock}

/-- **The flat engine.** A flat multiplier `μ` at a block `b` gives a real Jacquet functional
`ψ = ℓ_μ` with the exponents of `ds`; its Frobenius map `Ψ` lands in the principal series of
the characters `sgn^{e_i} |·|^{τ_i}`. If `τ_r - τ_{r+1} = k > 0` with `k + e_r + e_{r+1}` odd,
the binomial functional at `r` composed with `Ψ` gives `RealLinkedJacquetFunctionalExists`,
provided the `θ`-function `Σᶠ_j μ_j Φ^{(b)}_j(v)(r_r(θ))` of one `v` has a nonzero Fourier
coefficient in the parity class of `e_r + e_{r+1}`. -/
theorem exists_of_flat {b r : ℕ} (hb : b + 1 < n) (hr : r + 1 < n) {τ : Fin n → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds b (-1) * realPositionCharacter ds (b + 1) (-1))
    {μ : ℤ → ℂ}
    (hflat : ∀ (f : KF n ds) (j : ℤ), blockFourierCoefficient n b j f 1 ≠ 0 →
      μ (j + 2) * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) + j) =
        μ j * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) + j) ∧
      μ (j - 2) * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) - j) =
        μ j * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) - j))
    {σ : ℂ} (hsym : IsSymmetric ε σ μ) {e : Fin n → Fin 2}
    (he_off : ∀ i : Fin n, i ≠ ia hb → i ≠ ib hb →
      (-1 : ℂ) ^ (e i).val = realPositionCharacter ds i (-1))
    (he_p : (-1 : ℂ) ^ (e (ia hb)).val = realPositionCharacter ds b (-1) * σ)
    (he_q : (-1 : ℂ) ^ (e (ib hb)).val = realPositionCharacter ds (b + 1) (-1) * σ)
    {k : ℕ} (hk : 0 < k) (hτr : τ (ia hr) - τ (ib hr) = k)
    (hodd : Odd (k + (e (ia hr)).val + (e (ib hr)).val))
    (v : KF n ds)
    (hv : coeff ((par hr e : ℕ) : ℤ) (fun θ => ∑ᶠ j : ℤ, μ j *
      blockFourierCoefficient n b j v (blockRotation n r θ)) ≠ 0) :
    RealLinkedJacquetFunctionalExists n ds := by
  have hψ := isRealJacquetFunctional_blockJacquet_flat hb hτ hpar hflat hsym he_off he_p he_q
  have hsign : ∀ (i : Fin n) (w : KF n ds),
      blockJacquet n ds b μ (realStandardRep n ds (signReflection n i) w) =
        (-1) ^ (e i).val * blockJacquet n ds b μ w := fun i w => (hψ.2 i w).2
  refine exists_of_comp (frobMap hψ) (frobMap_rep hψ) (frobMap_lie hψ) hr hk ?_ hodd v ?_
  · simp only [RealJacquetFrobenius.expo]
    linear_combination hτr
  · rw [blockFourierCoefficient_eq_coeff]
    have h : (fun θ : ℝ => ((frobMap hψ v : KF n _) : Langlands.GeneralLinear n ℝ → ℂ)
        (blockRotation n r θ * 1)) = (2 * (Real.pi : ℂ))⁻¹ • fun θ => ∑ᶠ j : ℤ, μ j *
          blockFourierCoefficient n b j v (blockRotation n r θ) := by
      funext θ
      rw [frobMap_coe, mul_one,
        frobFun_apply_of_mem hsign v (blockRotation_mem_unitaryCompact n r θ)]
      rfl
    rw [h, coeff_smul]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) hv

theorem isSymmetric_one (ε : ℤ) : IsSymmetric ε 1 (fun _ : ℤ => (1 : ℂ)) :=
  fun _ _ => (one_mul _).symm

theorem isSymmetric_sign (ε : ℤ) : IsSymmetric ε (-1) (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) :=
  fun k _ => by simp [Int.sign_neg]

/-- **The sign multiplier is flat at an induction block.** If the modes `j` of the module at
the block `b` satisfy `|j| ≥ w` and `j ≡ w + 1 (mod 2)`, and `δ = w + 1`, then `sgn` is flat:
`|j| ≥ w + 1`, and `sgn(j ± 2) = sgn(j)` unless `δ ± j = 0`. -/
theorem flat_sign {b : ℕ} (hb : b + 1 < n) {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds b (-1) * realPositionCharacter ds (b + 1) (-1))
    {w : ℕ} (hεw : Even (ε - w - 1))
    (hwin : ∀ (f : KF n ds) (j : ℤ), |j| < w → blockFourierCoefficient n b j f 1 = 0)
    {δ : ℂ} (hδ : δ = (w : ℂ) + 1) (f : KF n ds) (j : ℤ)
    (hj : blockFourierCoefficient n b j f 1 ≠ 0) :
    (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) (j + 2) * (δ + j) =
        (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) j * (δ + j) ∧
      (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) (j - 2) * (δ - j) =
        (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) j * (δ - j) := by
  have h1 : (w : ℤ) ≤ |j| := not_lt.mp fun h => hj (hwin f j h)
  have h2 : Even (j - ε) := by
    by_contra h
    exact hj (blockFourierCoefficient_eq_zero_of_not_even hb hpar f h 1)
  rw [le_abs] at h1
  rw [Int.even_iff] at h2 hεw
  have hplus : ∀ m : ℤ, (w : ℤ) + 1 + m = 0 → δ + m = 0 := fun m hm => by
    rw [hδ]
    exact_mod_cast hm
  have hminus : ∀ m : ℤ, (w : ℤ) + 1 - m = 0 → δ - m = 0 := fun m hm => by
    rw [hδ]
    exact_mod_cast hm
  simp only
  rcases lt_trichotomy j 0 with hneg | hzero | hpos
  · have hs : j.sign = -1 := Int.sign_eq_neg_one_of_neg hneg
    refine ⟨?_, ?_⟩
    · by_cases h3 : j + 2 < 0
      · rw [hs, Int.sign_eq_neg_one_of_neg h3]
      · rw [hplus j (by omega), mul_zero, mul_zero]
    · rw [hs, Int.sign_eq_neg_one_of_neg (by omega)]
  · subst hzero
    omega
  · have hs : j.sign = 1 := Int.sign_eq_one_of_pos hpos
    refine ⟨?_, ?_⟩
    · rw [hs, Int.sign_eq_one_of_pos (by omega)]
    · by_cases h3 : 0 < j - 2
      · rw [hs, Int.sign_eq_one_of_pos h3]
      · rw [hminus j (by omega), mul_zero, mul_zero]

end Engine

/-! ## Test vectors -/

section TestVector

open TranslateFinite PrincipalSeriesExtension GramFormula

/-! ### Entries of rotated matrices -/

variable {b : ℕ}

theorem rot_mul_ia (hb : b + 1 < n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) (c : Fin n) :
    ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) (ia hb) c =
      Real.cos φ * κ (ia hb) c - Real.sin φ * κ (ib hb) c := by
  rw [blockRotation_val_eq hb, rotMatrix_mul_apply hb, blockProj, rotationGenerator_eq hb]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ (ia_ne_ib hb),
    one_mul]
  ring

theorem rot_mul_ib (hb : b + 1 < n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) (c : Fin n) :
    ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) (ib hb) c =
      Real.sin φ * κ (ia hb) c + Real.cos φ * κ (ib hb) c := by
  rw [blockRotation_val_eq hb, rotMatrix_mul_apply hb, blockProj, rotationGenerator_eq hb]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ (ia_ne_ib hb).symm,
    one_mul]
  ring

theorem rot_mul_of_ne (hb : b + 1 < n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) {i : Fin n}
    (h1 : i ≠ ia hb) (h2 : i ≠ ib hb) (c : Fin n) :
    ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) i c = κ i c := by
  rw [blockRotation_val_eq hb, rotMatrix_mul_apply hb, blockProj, rotationGenerator_eq hb]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ h1, Matrix.single_mul_apply_of_ne _ _ _ _ _ h2]
  ring

/-! ### The complex coordinates of a block -/

/-- `Z_c(κ) = κ_{b,c} + i κ_{b+1,c}`: the entries of column `c` in the rows of the block `b`,
as a complex number. -/
def zp (hb : b + 1 < n) (c : Fin n) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  (κ (ia hb) c : ℂ) + Complex.I * (κ (ib hb) c : ℂ)

/-- The conjugate `Z̄_c(κ) = κ_{b,c} - i κ_{b+1,c}`. -/
def zm (hb : b + 1 < n) (c : Fin n) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  (κ (ia hb) c : ℂ) - Complex.I * (κ (ib hb) c : ℂ)

theorem expMode_one_eq (φ : ℝ) : expMode 1 φ = Real.cos φ + Complex.I * Real.sin φ := by
  have h : ((1 : ℤ) : ℂ) * (φ : ℂ) * Complex.I = (φ : ℂ) * Complex.I := by push_cast; ring
  rw [expMode, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem expMode_neg_one_eq (φ : ℝ) :
    expMode (-1) φ = Real.cos φ - Complex.I * Real.sin φ := by
  have h : ((-1 : ℤ) : ℂ) * (φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [expMode, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

theorem zp_rot (hb : b + 1 < n) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zp hb c ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      expMode 1 φ * zp hb c κ := by
  rw [zp, zp, rot_mul_ia, rot_mul_ib, expMode_one_eq]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  linear_combination (-(Real.sin φ : ℂ) * (κ (ib hb) c : ℂ)) * Complex.I_sq

theorem zm_rot (hb : b + 1 < n) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zm hb c ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      expMode (-1) φ * zm hb c κ := by
  rw [zm, zm, rot_mul_ia, rot_mul_ib, expMode_neg_one_eq]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  linear_combination (-(Real.sin φ : ℂ) * (κ (ib hb) c : ℂ)) * Complex.I_sq

/-- The block factor `Z_c^m Z_{c'} + Z̄_c^m Z̄_{c'}` of degree `m + 1` at the block `b`. -/
def bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  zp hb c κ ^ m * zp hb c' κ + zm hb c κ ^ m * zm hb c' κ

theorem expMode_pow_mul (k : ℤ) (m : ℕ) (φ : ℝ) :
    expMode k φ ^ m * expMode k φ = expMode (((m : ℤ) + 1) * k) φ := by
  simp only [expMode, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Under the rotations of its block, the block factor has the two modes `±(m + 1)`. -/
theorem bf_rot (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    bf hb c c' m ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      expMode ((m : ℤ) + 1) φ * (zp hb c κ ^ m * zp hb c' κ) +
        expMode (-((m : ℤ) + 1)) φ * (zm hb c κ ^ m * zm hb c' κ) := by
  have h1 := expMode_pow_mul 1 m φ
  have h2 := expMode_pow_mul (-1) m φ
  rw [mul_one] at h1
  rw [mul_neg_one] at h2
  rw [bf, zp_rot, zp_rot, zm_rot, zm_rot, mul_pow, mul_pow, ← h1, ← h2]
  ring

/-- Rows outside the block `b'` are not moved by the rotations of `b'`. -/
theorem zp_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zp hb c ((blockRotation n b' φ : Matrix (Fin n) (Fin n) ℝ) * κ) = zp hb c κ := by
  have h1 : ia hb ≠ ia hb' := fun h => by simp [ia, Fin.ext_iff] at h; omega
  have h2 : ia hb ≠ ib hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h3 : ib hb ≠ ia hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h4 : ib hb ≠ ib hb' := fun h => by simp [ib, Fin.ext_iff] at h; omega
  rw [zp, zp, rot_mul_of_ne hb' φ κ h1 h2, rot_mul_of_ne hb' φ κ h3 h4]

theorem zm_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zm hb c ((blockRotation n b' φ : Matrix (Fin n) (Fin n) ℝ) * κ) = zm hb c κ := by
  have h1 : ia hb ≠ ia hb' := fun h => by simp [ia, Fin.ext_iff] at h; omega
  have h2 : ia hb ≠ ib hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h3 : ib hb ≠ ia hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h4 : ib hb ≠ ib hb' := fun h => by simp [ib, Fin.ext_iff] at h; omega
  rw [zm, zm, rot_mul_of_ne hb' φ κ h1 h2, rot_mul_of_ne hb' φ κ h3 h4]

theorem bf_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (c c' : Fin n) (m : ℕ) (φ : ℝ)
    (κ : Matrix (Fin n) (Fin n) ℝ) :
    bf hb c c' m ((blockRotation n b' φ : Matrix (Fin n) (Fin n) ℝ) * κ) = bf hb c c' m κ := by
  rw [bf, bf, zp_rot_of_disjoint hb hb' hd, zp_rot_of_disjoint hb hb' hd,
    zm_rot_of_disjoint hb hb' hd, zm_rot_of_disjoint hb hb' hd]

/-! ### Two modes -/

/-- The Fourier coefficients of `e^{iNφ} A + e^{-iNφ} B`. -/
theorem coeff_two_mode (N : ℤ) (A B : ℂ) (j : ℤ) :
    coeff j (fun φ => expMode N φ * A + expMode (-N) φ * B) =
      (if N = j then 2 * (Real.pi : ℂ) * A else 0) +
        (if -N = j then 2 * (Real.pi : ℂ) * B else 0) := by
  have h : (fun φ => expMode N φ * A + expMode (-N) φ * B) = A • expMode N + B • expMode (-N) := by
    funext φ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, coeff_add ((continuous_expMode N).const_smul A) ((continuous_expMode _).const_smul B),
    coeff_smul, coeff_smul, coeff_expMode, coeff_expMode]
  split_ifs <;> ring

theorem finsum_two_mode {N : ℤ} (hN : N ≠ 0) (A B : ℂ) (μ : ℤ → ℂ) :
    ∑ᶠ j : ℤ, μ j * ((if N = j then 2 * (Real.pi : ℂ) * A else 0) +
        (if -N = j then 2 * (Real.pi : ℂ) * B else 0)) =
      2 * (Real.pi : ℂ) * (μ N * A + μ (-N) * B) := by
  have h1 : N ≠ -N := by omega
  have h2 : -N ≠ N := by omega
  rw [finsum_eq_sum_of_support_subset (s := {N, -N}) _ ?_]
  · rw [Finset.sum_pair h1]
    simp only [h1, h2, ↓reduceIte]
    ring
  · intro j hj
    simp only [Function.mem_support] at hj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra h
    push Not at h
    apply hj
    have e1 : N ≠ j := fun e => h.1 e.symm
    have e2 : -N ≠ j := fun e => h.2 e.symm
    simp only [e1, e2, ↓reduceIte]
    ring

/-- **Two modes.** If `φ ↦ f(r_b(φ) g)` is `e^{iNφ} A + e^{-iNφ} B` with `N ≠ 0`, then
`Σᶠ_j μ_j Φ_j(f)(g) = 2π (μ_N A + μ_{-N} B)`. -/
theorem finsum_blockFourier_two_mode {f : Langlands.GeneralLinear n ℝ → ℂ}
    {g : Langlands.GeneralLinear n ℝ} {N : ℤ} (hN : N ≠ 0) {A B : ℂ}
    (hf : ∀ φ, f (blockRotation n b φ * g) = expMode N φ * A + expMode (-N) φ * B)
    (μ : ℤ → ℂ) :
    ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n b j f g =
      2 * (Real.pi : ℂ) * (μ N * A + μ (-N) * B) := by
  have h : (fun φ => f (blockRotation n b φ * g)) =
      fun φ => expMode N φ * A + expMode (-N) φ * B := funext hf
  simp_rw [blockFourierCoefficient_eq_coeff, h, coeff_two_mode]
  exact finsum_two_mode hN A B μ

theorem coeff_two_mode_eq_zero {N : ℤ} (A B : ℂ) {j : ℤ} (hj : |j| < |N|) :
    coeff j (fun φ => expMode N φ * A + expMode (-N) φ * B) = 0 := by
  have h1 : N ≠ j := fun h => by rw [h] at hj; exact lt_irrefl _ hj
  have h2 : -N ≠ j := fun h => by rw [← h, abs_neg] at hj; exact lt_irrefl _ hj
  rw [coeff_two_mode]
  simp only [h1, h2, ↓reduceIte, add_zero]

/-! ### Signs -/

/-- `F(diag(s) κ) = (∏ s_i^{q_i}) F(κ)` for all sign vectors `s`. -/
def IsSignEq (q : Fin n → ℕ) (F : Matrix (Fin n) (Fin n) ℝ → ℂ) : Prop :=
  ∀ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ κ : Matrix (Fin n) (Fin n) ℝ,
    F (Matrix.diagonal s * κ) = (∏ i, ((s i : ℝ) : ℂ) ^ q i) * F κ

theorem isSignEq_mul {q q' : Fin n → ℕ} {F G : Matrix (Fin n) (Fin n) ℝ → ℂ}
    (hF : IsSignEq q F) (hG : IsSignEq q' G) : IsSignEq (q + q') (fun κ => F κ * G κ) := by
  intro s hs κ
  dsimp only
  rw [hF s hs κ, hG s hs κ]
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

theorem isSignEq_pow {q : Fin n → ℕ} {F : Matrix (Fin n) (Fin n) ℝ → ℂ}
    (hF : IsSignEq q F) (m : ℕ) : IsSignEq (m • q) (fun κ => F κ ^ m) := by
  intro s hs κ
  dsimp only
  rw [hF s hs κ, mul_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]

theorem prod_pow_single (s : Fin n → ℝ) (i : Fin n) (m : ℕ) :
    ∏ j, ((s j : ℝ) : ℂ) ^ (Pi.single i m : Fin n → ℕ) j = ((s i : ℝ) : ℂ) ^ m := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem isSignEq_entry (i c : Fin n) :
    IsSignEq (Pi.single i 1) (fun κ => ((κ i c : ℝ) : ℂ)) := by
  intro s _ κ
  dsimp only
  rw [prod_pow_single, Matrix.diagonal_mul]
  push_cast
  ring

theorem zp_diag (hb : b + 1 < n) (c : Fin n) (s : Fin n → ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zp hb c (Matrix.diagonal s * κ) =
      (s (ia hb) : ℂ) * κ (ia hb) c + Complex.I * ((s (ib hb) : ℂ) * κ (ib hb) c) := by
  rw [zp, Matrix.diagonal_mul, Matrix.diagonal_mul]
  push_cast
  ring

theorem zm_diag (hb : b + 1 < n) (c : Fin n) (s : Fin n → ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zm hb c (Matrix.diagonal s * κ) =
      (s (ia hb) : ℂ) * κ (ia hb) c - Complex.I * ((s (ib hb) : ℂ) * κ (ib hb) c) := by
  rw [zm, Matrix.diagonal_mul, Matrix.diagonal_mul]
  push_cast
  ring

/-- The block factor of degree `m + 1` transforms by `s_b^{m + 1}`. -/
theorem isSignEq_bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) :
    IsSignEq (Pi.single (ia hb) (m + 1)) (bf hb c c' m) := by
  intro s hs κ
  rw [prod_pow_single, bf, bf, zp_diag, zp_diag, zm_diag, zm_diag]
  rcases hs (ia hb) with h1 | h1 <;> rcases hs (ib hb) with h2 | h2 <;> rw [h1, h2] <;>
    push_cast
  · simp only [one_mul, one_pow, zp, zm]
  · simp only [one_mul, one_pow, zp, zm]
    ring
  · have e1 : (-1 * (κ (ia hb) c : ℂ) + Complex.I * (1 * (κ (ib hb) c : ℂ))) = -zm hb c κ := by
      rw [zm]; ring
    have e2 : (-1 * (κ (ia hb) c : ℂ) - Complex.I * (1 * (κ (ib hb) c : ℂ))) = -zp hb c κ := by
      rw [zp]; ring
    have e3 : (-1 * (κ (ia hb) c' : ℂ) + Complex.I * (1 * (κ (ib hb) c' : ℂ))) = -zm hb c' κ := by
      rw [zm]; ring
    have e4 : (-1 * (κ (ia hb) c' : ℂ) - Complex.I * (1 * (κ (ib hb) c' : ℂ))) = -zp hb c' κ := by
      rw [zp]; ring
    rw [e1, e2, e3, e4, neg_pow, neg_pow (zp hb c κ), pow_succ]
    ring
  · have e1 : (-1 * (κ (ia hb) c : ℂ) + Complex.I * (-1 * (κ (ib hb) c : ℂ))) = -zp hb c κ := by
      rw [zp]; ring
    have e2 : (-1 * (κ (ia hb) c : ℂ) - Complex.I * (-1 * (κ (ib hb) c : ℂ))) = -zm hb c κ := by
      rw [zm]; ring
    have e3 : (-1 * (κ (ia hb) c' : ℂ) + Complex.I * (-1 * (κ (ib hb) c' : ℂ))) =
        -zp hb c' κ := by
      rw [zp]; ring
    have e4 : (-1 * (κ (ia hb) c' : ℂ) - Complex.I * (-1 * (κ (ib hb) c' : ℂ))) =
        -zm hb c' κ := by
      rw [zm]; ring
    rw [e1, e2, e3, e4, neg_pow, neg_pow (zm hb c κ), pow_succ]
    ring

/-! ### Translate-finiteness and continuity -/

theorem isTranslateFinite_zp (hb : b + 1 < n) (c : Fin n) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => zp hb c (κ : Matrix (Fin n) (Fin n) ℝ)) :=
  isTranslateFinite_add (isTranslateFinite_entry (ia hb, c))
    (isTranslateFinite_smul (isTranslateFinite_entry (ib hb, c)) Complex.I)

theorem isTranslateFinite_zm (hb : b + 1 < n) (c : Fin n) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => zm hb c (κ : Matrix (Fin n) (Fin n) ℝ)) := by
  have h := isTranslateFinite_add (isTranslateFinite_entry (ia hb, c))
    (isTranslateFinite_smul (isTranslateFinite_entry (ib hb, c)) (-Complex.I))
  have e : (fun κ : Matrix.unitaryGroup (Fin n) ℝ => zm hb c (κ : Matrix (Fin n) (Fin n) ℝ)) =
      fun κ : Matrix.unitaryGroup (Fin n) ℝ => (((κ : Matrix (Fin n) (Fin n) ℝ) (ia hb, c).1 (ia hb, c).2 : ℝ) : ℂ) +
        -Complex.I * (((κ : Matrix (Fin n) (Fin n) ℝ) (ib hb, c).1 (ib hb, c).2 : ℝ) : ℂ) := by
    funext κ
    rw [zm]
    ring
  rw [e]
  exact h

theorem isTranslateFinite_bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => bf hb c c' m (κ : Matrix (Fin n) (Fin n) ℝ)) :=
  isTranslateFinite_add
    (isTranslateFinite_mul (isTranslateFinite_pow (isTranslateFinite_zp hb c) m)
      (isTranslateFinite_zp hb c'))
    (isTranslateFinite_mul (isTranslateFinite_pow (isTranslateFinite_zm hb c) m)
      (isTranslateFinite_zm hb c'))

theorem continuous_entry (i c : Fin n) :
    Continuous fun κ : Matrix (Fin n) (Fin n) ℝ => ((κ i c : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((continuous_apply c).comp (continuous_apply i))

theorem continuous_zp (hb : b + 1 < n) (c : Fin n) : Continuous (zp hb c) :=
  (continuous_entry _ _).add (continuous_const.mul (continuous_entry _ _))

theorem continuous_zm (hb : b + 1 < n) (c : Fin n) : Continuous (zm hb c) :=
  (continuous_entry _ _).sub (continuous_const.mul (continuous_entry _ _))

theorem continuous_bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) : Continuous (bf hb c c' m) :=
  (((continuous_zp hb c).pow m).mul (continuous_zp hb c')).add
    (((continuous_zm hb c).pow m).mul (continuous_zm hb c'))

end TestVector

/-! ## Test vectors from functions on `O(n)` -/

section Extension

open TranslateFinite PrincipalSeriesExtension GramFormula

theorem signReal_cases (x : ℝ) : signReal x = 1 ∨ signReal x = -1 := by
  unfold signReal
  split_ifs <;> simp

/-- **Test vectors.** A continuous `O(n)`-finite function `F` on matrices which transforms under
the sign matrices like the position characters of `ds` and whose block Fourier coefficients of
weight `|k| < |m|` vanish on `O(n)` at every induction block of weight `m` is the restriction to
`O(n)` of an `O(n)`-finite function of the standard module of `ds`. -/
theorem exists_KF {ds : List RealBlock} (hN : realRank ds = n)
    {F : Matrix (Fin n) (Fin n) ℝ → ℂ} (hFc : Continuous F)
    (hFt : IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => F (κ : Matrix (Fin n) (Fin n) ℝ)))
    {q : Fin n → ℕ} (hq : IsSignEq q F)
    (hs : ∀ i : Fin n, (-1 : ℂ) ^ q i = realPositionCharacter ds i (-1))
    (hwin : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ k : ℤ, |k| < |d.weight| → ∀ κ : Matrix (Fin n) (Fin n) ℝ,
        κ ∈ Matrix.unitaryGroup (Fin n) ℝ →
        coeff k (fun φ => F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) = 0) :
    ∃ v : KF n ds, ∀ g ∈ unitaryCompact ℝ n,
      (v : Langlands.GeneralLinear n ℝ → ℂ) g = F (g : Matrix (Fin n) (Fin n) ℝ) := by
  have hsgn : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      F ((signDiagonal (fun i => (a i : ℝ)) * κ : Matrix.unitaryGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) =
        principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) *
          F (κ : Matrix (Fin n) (Fin n) ℝ) := by
    intro a κ
    have hsd : ((signDiagonal (fun i => (a i : ℝ)) * κ : Matrix.unitaryGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) =
        Matrix.diagonal (fun i => signReal (a i : ℝ)) * (κ : Matrix (Fin n) (Fin n) ℝ) := rfl
    rw [hsd, hq _ (fun i => signReal_cases _) _, JacquetKernel.principalSeriesCharacter_sign]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold signReal signUnit
    split_ifs
    · simp [RealStrictCharacterLanglandsQuotient.realPositionCharacter_one]
    · rw [← hs i]
      push_cast
      rfl
  obtain ⟨f, hf, hfK⟩ := principalSeriesExtension n ds
    (fun κ : Matrix.unitaryGroup (Fin n) ℝ => F (κ : Matrix (Fin n) (Fin n) ℝ))
    (hFc.comp continuous_subtype_val) hFt hsgn
  have hfK' : ∀ g ∈ unitaryCompact ℝ n, f g = F (g : Matrix (Fin n) (Fin n) ℝ) := by
    intro g hg
    have h := hfK ⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩
    have hg' : (Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩ :
        Matrix.unitaryGroup (Fin n) ℝ)) = g := Units.ext rfl
    rw [hg'] at h
    exact h
  refine ⟨⟨f, mem_realStandardModule_of_unitaryCompact hN hf.1 ?_, hf.2⟩, hfK'⟩
  intro p d hd k hk κ hκ
  rw [blockFourierCoefficient_eq_coeff]
  have h : (fun θ => f (blockRotation n p θ * κ)) = fun θ =>
      F ((blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)) := by
    funext θ
    rw [hfK' _ ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hκ)]
    rfl
  rw [h]
  exact hwin p d hd k hk _ hκ

/-- Two modes `±N` of `F` along the rotations of `p` kill the coefficients of weight `|k| < |N|`. -/
theorem coeff_eq_zero_of_two_mode {F A B : Matrix (Fin n) (Fin n) ℝ → ℂ} {p : ℕ} {N : ℤ}
    (hAB : ∀ (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ),
      F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
        expMode N φ * A κ + expMode (-N) φ * B κ)
    {k : ℤ} (hk : |k| < |N|) (κ : Matrix (Fin n) (Fin n) ℝ) :
    coeff k (fun φ => F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) = 0 := by
  have h : (fun φ => F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) =
      fun φ => expMode N φ * A κ + expMode (-N) φ * B κ := funext fun φ => hAB φ κ
  rw [h]
  exact coeff_two_mode_eq_zero _ _ hk

/-- **The assembly.** The flat engine `exists_of_flat` applied to the test vector of a function
`F` on `O(n)` as in `exists_KF` which has the two modes `±N` along the rotations of `b`, with
`θ ↦ μ_N A(r_r θ) + μ_{-N} B(r_r θ)` equal to `C cos^m θ`, `C ≠ 0`, `m ≤ 2` of the parity
of `e_r + e_{r+1}`. -/
theorem exists_of_flat_test {ds : List RealBlock} (hN : realRank ds = n) {b r : ℕ}
    (hb : b + 1 < n) (hr : r + 1 < n) {τ : Fin n → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ds b (-1) * realPositionCharacter ds (b + 1) (-1))
    {μ : ℤ → ℂ}
    (hflat : ∀ (f : KF n ds) (j : ℤ), blockFourierCoefficient n b j f 1 ≠ 0 →
      μ (j + 2) * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) + j) =
        μ j * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) + j) ∧
      μ (j - 2) * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) - j) =
        μ j * (((τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
          (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ))) - j))
    {σ : ℂ} (hsym : IsSymmetric ε σ μ) {e : Fin n → Fin 2}
    (he_off : ∀ i : Fin n, i ≠ ia hb → i ≠ ib hb →
      (-1 : ℂ) ^ (e i).val = realPositionCharacter ds i (-1))
    (he_p : (-1 : ℂ) ^ (e (ia hb)).val = realPositionCharacter ds b (-1) * σ)
    (he_q : (-1 : ℂ) ^ (e (ib hb)).val = realPositionCharacter ds (b + 1) (-1) * σ)
    {k : ℕ} (hk : 0 < k) (hτr : τ (ia hr) - τ (ib hr) = k)
    (hodd : Odd (k + (e (ia hr)).val + (e (ib hr)).val))
    {F : Matrix (Fin n) (Fin n) ℝ → ℂ} (hFc : Continuous F)
    (hFt : IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => F (κ : Matrix (Fin n) (Fin n) ℝ)))
    {q : Fin n → ℕ} (hq : IsSignEq q F)
    (hs : ∀ i : Fin n, (-1 : ℂ) ^ q i = realPositionCharacter ds i (-1))
    (hwin : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ k : ℤ, |k| < |d.weight| → ∀ κ : Matrix (Fin n) (Fin n) ℝ,
        κ ∈ Matrix.unitaryGroup (Fin n) ℝ →
        coeff k (fun φ => F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) = 0)
    {N : ℤ} (hN0 : N ≠ 0) {A B : Matrix (Fin n) (Fin n) ℝ → ℂ}
    (hAB : ∀ (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ),
      F ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
        expMode N φ * A κ + expMode (-N) φ * B κ)
    {C : ℂ} (hC : C ≠ 0) {m : ℕ} (hm : m ≤ 2) (hpm : m % 2 = par hr e)
    (hcos : ∀ θ : ℝ, μ N * A (blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ) +
        μ (-N) * B (blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ) =
      C * (Real.cos θ : ℂ) ^ m) :
    RealLinkedJacquetFunctionalExists n ds := by
  obtain ⟨v, hv⟩ := exists_KF hN hFc hFt hq hs hwin
  refine exists_of_flat hb hr hτ hpar hflat hsym he_off he_p he_q hk hτr hodd v ?_
  have h : (fun θ => ∑ᶠ j : ℤ, μ j *
      blockFourierCoefficient n b j (v : Langlands.GeneralLinear n ℝ → ℂ)
        (blockRotation n r θ)) =
      (2 * (Real.pi : ℂ) * C) • fun θ : ℝ => (Real.cos θ : ℂ) ^ m := by
    funext θ
    rw [finsum_blockFourier_two_mode hN0
      (A := A (blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ))
      (B := B (blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ)) ?_ μ, hcos θ]
    · simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · intro φ
      rw [hv _ ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n b φ)
        (blockRotation_mem_unitaryCompact n r θ))]
      exact hAB φ _
  rw [h, coeff_smul, ← hpm]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hC) (coeff_cos_pow_ne_zero hm)

end Extension

/-! ## Linked pairs straddling an induction block -/

section Pairs

open TranslateFinite PrincipalSeriesExtension GramFormula

theorem character_neg_one (c : RealCharacterData) :
    (c.character (-1) : ℂ) = (-1 : ℂ) ^ c.parity.val := by
  rw [c.character_eq]
  simp

theorem abs_lt_natAbs_succ {j m : ℤ} (h : |j| < |m|) : |j| < |((m.natAbs : ℕ) : ℤ) + 1| := by
  have h1 : |((m.natAbs : ℕ) : ℤ) + 1| = (m.natAbs : ℤ) + 1 := abs_of_nonneg (by positivity)
  rw [h1]
  rw [Int.abs_eq_natAbs m] at h
  omega

/-- The linking of an induction block `d` and a character `c` with `Re t(c) ≤ Re t(d)`:
`t(d) - t(c) = |m|/2 + k` with `k ≥ 1`. -/
theorem linked_induced_character {d : ComplexCharacterData} {c : RealCharacterData}
    (hw : d.weight ≠ 0)
    (hexp : realBlockExponent (RealBlock.character c) ≤ realBlockExponent (RealBlock.induced d))
    (hun : ¬ AreRealBlocksUnlinked (RealBlock.induced d) (RealBlock.character c)) :
    ∃ k : ℕ, 0 < k ∧ d.exponent - c.exponent = (d.weight.natAbs : ℂ) / 2 + k := by
  have h : MoeglinDatum.IsLinked (.discrete d.weight.natAbs d.exponent)
      (.character c.parity c.exponent) := by
    by_contra h
    exact hun fun a ha b hb => by
      simp only [realBlockMoeglinData, hw, ↓reduceIte, List.mem_singleton] at ha hb
      subst ha hb
      exact h
  obtain ⟨k, hk, h | h⟩ := h
  · exact ⟨k, hk, h⟩
  · exfalso
    have h' : c.exponent - d.exponent = (((d.weight.natAbs : ℝ) / 2 + k : ℝ) : ℂ) := by
      rw [h]
      push_cast
      ring
    have h1 := congrArg Complex.re h'
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    simp only [realBlockExponent] at hexp
    have h2 : (0 : ℝ) < k := by exact_mod_cast hk
    have h3 : (0 : ℝ) ≤ (d.weight.natAbs : ℝ) := Nat.cast_nonneg _
    linarith

/-- **An induction block followed by a linked character.** -/
theorem realInducedCharacterLinkedJacquetFunctional :
    RealInducedCharacterLinkedJacquetFunctionalStatement := by
  intro d c hw hexp hun
  obtain ⟨k, hk, hlink⟩ := linked_induced_character hw hexp hun
  have hN : realRank [RealBlock.induced d, RealBlock.character c] = 3 := rfl
  have hb : 0 + 1 < 3 := by norm_num
  have hr : 1 + 1 < 3 := by norm_num
  have hτ := fun (i : Fin 3) (x : ℝ) =>
    realPositionCharacter_exp [RealBlock.induced d, RealBlock.character c] i x
  have hc0 : realPositionCharacter [RealBlock.induced d, RealBlock.character c] 0 (-1) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) := realInducedFirstCharacter_neg_one d
  have hc1 : realPositionCharacter [RealBlock.induced d, RealBlock.character c] 1 (-1) = 1 :=
    realInducedSecondCharacter_neg_one d
  have hc2 : realPositionCharacter [RealBlock.induced d, RealBlock.character c] 2 (-1) =
      (-1 : ℂ) ^ c.parity.val := character_neg_one c
  have hpar : (-1 : ℂ) ^ ((d.weight.natAbs : ℤ) + 1) =
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] 0 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.character c] 1 (-1) := by
    rw [hc0, hc1, mul_one, ← zpow_natCast]
    push_cast
    rfl
  have hτr : realPositionExponent [RealBlock.induced d, RealBlock.character c]
        ((ia hr : Fin 3) : ℕ) -
      realPositionExponent [RealBlock.induced d, RealBlock.character c]
        ((ib hr : Fin 3) : ℕ) = k := by
    show (d.exponent - (d.weight.natAbs : ℂ) / 2) - c.exponent = k
    linear_combination hlink
  -- the test functions
  have hFc : ∀ c' : Fin 3, Continuous fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
      bf hb 0 c' d.weight.natAbs κ * ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val := fun c' =>
    (continuous_bf hb 0 c' _).mul ((continuous_entry 2 2).pow _)
  have hFt : ∀ c' : Fin 3, IsTranslateFinite
      (id : Matrix.unitaryGroup (Fin 3) ℝ → Matrix.unitaryGroup (Fin 3) ℝ)
      (fun κ => (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val)
          (κ : Matrix (Fin 3) (Fin 3) ℝ)) := fun c' =>
    isTranslateFinite_mul (isTranslateFinite_bf hb 0 c' _)
      (isTranslateFinite_pow (isTranslateFinite_entry ((2 : Fin 3), (2 : Fin 3))) _)
  have hq : ∀ c' : Fin 3, IsSignEq
      (Pi.single (ia hb) (d.weight.natAbs + 1) + c.parity.val • Pi.single (2 : Fin 3) 1)
      (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val) := fun c' =>
    isSignEq_mul (isSignEq_bf hb 0 c' _) (isSignEq_pow (isSignEq_entry 2 2) _)
  have hs : ∀ i : Fin 3, (-1 : ℂ) ^
      ((Pi.single (ia hb) (d.weight.natAbs + 1) + c.parity.val • Pi.single (2 : Fin 3) 1 :
        Fin 3 → ℕ) i) =
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] i (-1) := by
    intro i
    fin_cases i
    · simp [ia, hc0]
    · simp [ia, hc1]
    · simp [ia, hc2]
  have hAB : ∀ (c' : Fin 3) (φ : ℝ) (κ : Matrix (Fin 3) (Fin 3) ℝ),
      (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val)
        ((blockRotation 3 0 φ : Matrix (Fin 3) (Fin 3) ℝ) * κ) =
      expMode ((d.weight.natAbs : ℤ) + 1) φ *
          (fun κ : Matrix (Fin 3) (Fin 3) ℝ => zp hb 0 κ ^ d.weight.natAbs * zp hb c' κ *
            ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val) κ +
        expMode (-((d.weight.natAbs : ℤ) + 1)) φ *
          (fun κ : Matrix (Fin 3) (Fin 3) ℝ => zm hb 0 κ ^ d.weight.natAbs * zm hb c' κ *
            ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val) κ := by
    intro c' φ κ
    dsimp only
    rw [bf_rot, rot_mul_of_ne hb φ κ (i := 2) (by simp [ia, Fin.ext_iff])
      (by simp [ib, Fin.ext_iff])]
    ring
  have hwin : ∀ (c' : Fin 3) (p : ℕ) (d' : ComplexCharacterData),
      realInducedBlockAt [RealBlock.induced d, RealBlock.character c] p = some d' →
      ∀ j : ℤ, |j| < |d'.weight| → ∀ κ : Matrix (Fin 3) (Fin 3) ℝ,
        κ ∈ Matrix.unitaryGroup (Fin 3) ℝ →
        coeff j (fun φ => (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
          bf hb 0 c' d.weight.natAbs κ * ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val)
            ((blockRotation 3 p φ : Matrix (Fin 3) (Fin 3) ℝ) * κ)) = 0 := by
    intro c' p d' hd j hj κ _
    rcases p with _ | _ | _ | p
    · simp only [realInducedBlockAt, Option.some.injEq] at hd
      subst hd
      exact coeff_eq_zero_of_two_mode (F := fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * ((κ 2 2 : ℝ) : ℂ) ^ c.parity.val) (hAB c')
        (abs_lt_natAbs_succ hj) κ
    · simp [realInducedBlockAt] at hd
    · simp [realInducedBlockAt] at hd
    · simp [realInducedBlockAt] at hd
  have hN0 : ((d.weight.natAbs : ℤ) + 1) ≠ 0 := by omega
  have hrot : ∀ θ : ℝ,
      zp hb 0 (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) = 1 ∧
      zm hb 0 (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) = 1 ∧
      zp hb 1 (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) = Complex.I * Real.cos θ ∧
      zm hb 1 (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) = -(Complex.I * Real.cos θ) ∧
      (((blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) 2 2 : ℝ) : ℂ) = Real.cos θ := by
    intro θ
    simp only [zp, zm, blockRotation_apply hr]
    simp [ia, ib]
  rcases Nat.even_or_odd (k + c.parity.val) with hev | hodd
  · -- the sign multiplier: the signs at the block are flipped
    refine exists_of_flat_test (τ := fun i => realPositionExponent
        [RealBlock.induced d, RealBlock.character c] i)
      (μ := fun j : ℤ => ((Int.sign j : ℤ) : ℂ))
      (e := ![⟨d.weight.natAbs % 2, Nat.mod_lt _ two_pos⟩, 1, c.parity]) hN hb hr hτ hpar
      (flat_sign hb hpar (w := d.weight.natAbs) ⟨0, by ring⟩
        (fun f j hj => (Submodule.mem_inf.mp f.2).1.2 0 d rfl j
          (by rwa [Int.abs_eq_natAbs d.weight]) 1) ?_)
      (isSymmetric_sign _) ?_ ?_ ?_ hk hτr ?_ (hFc 1) (hFt 1) (hq 1) hs (hwin 1) hN0 (hAB 1)
      (C := 2 * Complex.I) (by simp) (m := 1 + c.parity.val) (by omega) rfl ?_
    · show (realPositionExponent [RealBlock.induced d, RealBlock.character c] 0 +
          (((3 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) -
        (realPositionExponent [RealBlock.induced d, RealBlock.character c] 1 +
          (((3 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) = (d.weight.natAbs : ℂ) + 1
      show (d.exponent + (d.weight.natAbs : ℂ) / 2 + (((3 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) -
        (d.exponent - (d.weight.natAbs : ℂ) / 2 + (((3 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) =
          (d.weight.natAbs : ℂ) + 1
      push_cast
      ring
    · intro i h1 h2
      fin_cases i
      · exact absurd rfl h1
      · exact absurd rfl h2
      · show (-1 : ℂ) ^ c.parity.val = _
        exact hc2.symm
    · show (-1 : ℂ) ^ (d.weight.natAbs % 2) = _
      rw [hc0, ← neg_one_pow_eq_pow_mod_two, pow_succ]
      ring
    · show (-1 : ℂ) ^ 1 = realPositionCharacter [RealBlock.induced d, RealBlock.character c] 1 (-1) * -1
      rw [hc1]
      ring
    · show Odd (k + 1 + c.parity.val)
      rw [add_right_comm]
      exact hev.add_one
    · intro θ
      obtain ⟨h1, h2, h3, h4, h5⟩ := hrot θ
      have s1 : Int.sign ((d.weight.natAbs : ℤ) + 1) = 1 := Int.sign_eq_one_of_pos (by omega)
      have s2 : Int.sign (-((d.weight.natAbs : ℤ) + 1)) = -1 :=
        Int.sign_eq_neg_one_of_neg (by omega)
      simp only [h1, h2, h3, h4, h5, s1, s2]
      push_cast
      ring
  · -- the trivial multiplier
    refine exists_of_flat_test (τ := fun i => realPositionExponent
        [RealBlock.induced d, RealBlock.character c] i)
      (μ := fun _ : ℤ => (1 : ℂ))
      (e := ![⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩, 0, c.parity]) hN hb hr hτ hpar
      (fun _ _ _ => ⟨rfl, rfl⟩) (isSymmetric_one _) ?_ ?_ ?_ hk hτr ?_ (hFc 0) (hFt 0) (hq 0) hs
      (hwin 0) hN0 (hAB 0) (C := 2) (by simp) (m := c.parity.val) (by omega) ?_ ?_
    · intro i h1 h2
      fin_cases i
      · exact absurd rfl h1
      · exact absurd rfl h2
      · show (-1 : ℂ) ^ c.parity.val = _
        exact hc2.symm
    · show (-1 : ℂ) ^ ((d.weight.natAbs + 1) % 2) = _
      rw [hc0, ← neg_one_pow_eq_pow_mod_two, mul_one]
    · show (-1 : ℂ) ^ 0 = realPositionCharacter [RealBlock.induced d, RealBlock.character c] 1 (-1) * 1
      rw [hc1]
      ring
    · show Odd (k + 0 + c.parity.val)
      rwa [add_zero]
    · show c.parity.val % 2 = (0 + c.parity.val) % 2
      rw [zero_add]
    · intro θ
      obtain ⟨h1, h2, h3, h4, h5⟩ := hrot θ
      simp only [h1, h2, h5]
      ring

/-- The linking of a character `c` and an induction block `d` with `Re t(d) ≤ Re t(c)`:
`t(c) - t(d) = |m|/2 + k` with `k ≥ 1`. -/
theorem linked_character_induced {c : RealCharacterData} {d : ComplexCharacterData}
    (hw : d.weight ≠ 0)
    (hexp : realBlockExponent (RealBlock.induced d) ≤ realBlockExponent (RealBlock.character c))
    (hun : ¬ AreRealBlocksUnlinked (RealBlock.character c) (RealBlock.induced d)) :
    ∃ k : ℕ, 0 < k ∧ c.exponent - d.exponent = (d.weight.natAbs : ℂ) / 2 + k := by
  have h : MoeglinDatum.IsLinked (.character c.parity c.exponent)
      (.discrete d.weight.natAbs d.exponent) := by
    by_contra h
    exact hun fun a ha b hb => by
      simp only [realBlockMoeglinData, hw, ↓reduceIte, List.mem_singleton] at ha hb
      subst ha hb
      exact h
  obtain ⟨k, hk, h | h⟩ := h
  · exfalso
    have h' : d.exponent - c.exponent = (((d.weight.natAbs : ℝ) / 2 + k : ℝ) : ℂ) := by
      rw [h]
      push_cast
      ring
    have h1 := congrArg Complex.re h'
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    simp only [realBlockExponent] at hexp
    have h2 : (0 : ℝ) < k := by exact_mod_cast hk
    have h3 : (0 : ℝ) ≤ (d.weight.natAbs : ℝ) := Nat.cast_nonneg _
    linarith
  · exact ⟨k, hk, h⟩

/-- **A character followed by a linked induction block.** -/
theorem realCharacterInducedLinkedJacquetFunctional :
    RealCharacterInducedLinkedJacquetFunctionalStatement := by
  intro c d hw hexp hun
  obtain ⟨k, hk, hlink⟩ := linked_character_induced hw hexp hun
  have hN : realRank [RealBlock.character c, RealBlock.induced d] = 3 := rfl
  have hb : 1 + 1 < 3 := by norm_num
  have hr : 0 + 1 < 3 := by norm_num
  have hτ := fun (i : Fin 3) (x : ℝ) =>
    realPositionCharacter_exp [RealBlock.character c, RealBlock.induced d] i x
  have hc0 : realPositionCharacter [RealBlock.character c, RealBlock.induced d] 0 (-1) =
      (-1 : ℂ) ^ c.parity.val := character_neg_one c
  have hc1 : realPositionCharacter [RealBlock.character c, RealBlock.induced d] 1 (-1) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) := realInducedFirstCharacter_neg_one d
  have hc2 : realPositionCharacter [RealBlock.character c, RealBlock.induced d] 2 (-1) = 1 :=
    realInducedSecondCharacter_neg_one d
  have hpar : (-1 : ℂ) ^ ((d.weight.natAbs : ℤ) + 1) =
      realPositionCharacter [RealBlock.character c, RealBlock.induced d] 1 (-1) *
        realPositionCharacter [RealBlock.character c, RealBlock.induced d] 2 (-1) := by
    rw [hc1, hc2, mul_one, ← zpow_natCast]
    push_cast
    rfl
  have hτr : realPositionExponent [RealBlock.character c, RealBlock.induced d]
        ((ia hr : Fin 3) : ℕ) -
      realPositionExponent [RealBlock.character c, RealBlock.induced d]
        ((ib hr : Fin 3) : ℕ) = k := by
    show c.exponent - (d.exponent + (d.weight.natAbs : ℂ) / 2) = k
    linear_combination hlink
  have hδ : (realPositionExponent [RealBlock.character c, RealBlock.induced d] 1 +
        (((3 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) -
      (realPositionExponent [RealBlock.character c, RealBlock.induced d] 2 +
        (((3 : ℕ) : ℂ) - 1) / 2 - ((2 : ℕ) : ℂ)) = (d.weight.natAbs : ℂ) + 1 := by
    show (d.exponent + (d.weight.natAbs : ℂ) / 2 + (((3 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) -
      (d.exponent - (d.weight.natAbs : ℂ) / 2 + (((3 : ℕ) : ℂ) - 1) / 2 - ((2 : ℕ) : ℂ)) =
        (d.weight.natAbs : ℂ) + 1
    push_cast
    ring
  -- the test functions
  have hFc : ∀ c' : Fin 3, Continuous fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
      bf hb 2 c' d.weight.natAbs κ * ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val := fun c' =>
    (continuous_bf hb 2 c' _).mul ((continuous_entry 0 0).pow _)
  have hFt : ∀ c' : Fin 3, IsTranslateFinite
      (id : Matrix.unitaryGroup (Fin 3) ℝ → Matrix.unitaryGroup (Fin 3) ℝ)
      (fun κ => (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 2 c' d.weight.natAbs κ * ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val)
          (κ : Matrix (Fin 3) (Fin 3) ℝ)) := fun c' =>
    isTranslateFinite_mul (isTranslateFinite_bf hb 2 c' _)
      (isTranslateFinite_pow (isTranslateFinite_entry ((0 : Fin 3), (0 : Fin 3))) _)
  have hq : ∀ c' : Fin 3, IsSignEq
      (Pi.single (ia hb) (d.weight.natAbs + 1) + c.parity.val • Pi.single (0 : Fin 3) 1)
      (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 2 c' d.weight.natAbs κ * ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val) := fun c' =>
    isSignEq_mul (isSignEq_bf hb 2 c' _) (isSignEq_pow (isSignEq_entry 0 0) _)
  have hs : ∀ i : Fin 3, (-1 : ℂ) ^
      ((Pi.single (ia hb) (d.weight.natAbs + 1) + c.parity.val • Pi.single (0 : Fin 3) 1 :
        Fin 3 → ℕ) i) =
      realPositionCharacter [RealBlock.character c, RealBlock.induced d] i (-1) := by
    intro i
    fin_cases i
    · simp [ia, hc0]
    · simp [ia, hc1]
    · simp [ia, hc2]
  have hAB : ∀ (c' : Fin 3) (φ : ℝ) (κ : Matrix (Fin 3) (Fin 3) ℝ),
      (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 2 c' d.weight.natAbs κ * ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val)
        ((blockRotation 3 1 φ : Matrix (Fin 3) (Fin 3) ℝ) * κ) =
      expMode ((d.weight.natAbs : ℤ) + 1) φ *
          (fun κ : Matrix (Fin 3) (Fin 3) ℝ => zp hb 2 κ ^ d.weight.natAbs * zp hb c' κ *
            ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val) κ +
        expMode (-((d.weight.natAbs : ℤ) + 1)) φ *
          (fun κ : Matrix (Fin 3) (Fin 3) ℝ => zm hb 2 κ ^ d.weight.natAbs * zm hb c' κ *
            ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val) κ := by
    intro c' φ κ
    dsimp only
    rw [bf_rot, rot_mul_of_ne hb φ κ (i := 0) (by simp [ia])
      (by simp [ib, Fin.ext_iff])]
    ring
  have hwin : ∀ (c' : Fin 3) (p : ℕ) (d' : ComplexCharacterData),
      realInducedBlockAt [RealBlock.character c, RealBlock.induced d] p = some d' →
      ∀ j : ℤ, |j| < |d'.weight| → ∀ κ : Matrix (Fin 3) (Fin 3) ℝ,
        κ ∈ Matrix.unitaryGroup (Fin 3) ℝ →
        coeff j (fun φ => (fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
          bf hb 2 c' d.weight.natAbs κ * ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val)
            ((blockRotation 3 p φ : Matrix (Fin 3) (Fin 3) ℝ) * κ)) = 0 := by
    intro c' p d' hd j hj κ _
    rcases p with _ | _ | _ | p
    · simp [realInducedBlockAt] at hd
    · simp only [realInducedBlockAt, Option.some.injEq] at hd
      subst hd
      exact coeff_eq_zero_of_two_mode (F := fun κ : Matrix (Fin 3) (Fin 3) ℝ =>
        bf hb 2 c' d.weight.natAbs κ * ((κ 0 0 : ℝ) : ℂ) ^ c.parity.val) (hAB c')
        (abs_lt_natAbs_succ hj) κ
    · simp [realInducedBlockAt] at hd
    · simp [realInducedBlockAt] at hd
  have hN0 : ((d.weight.natAbs : ℤ) + 1) ≠ 0 := by omega
  have hrot : ∀ θ : ℝ,
      zp hb 2 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) = Complex.I ∧
      zm hb 2 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) = -Complex.I ∧
      zp hb 1 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) = Real.cos θ ∧
      zm hb 1 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) = Real.cos θ ∧
      (((blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) 0 0 : ℝ) : ℂ) = Real.cos θ := by
    intro θ
    simp only [zp, zm, blockRotation_apply hr]
    simp [ia, ib]
  have hI : ∀ p : ℕ, Complex.I ^ p ≠ 0 := fun p => pow_ne_zero _ Complex.I_ne_zero
  have hεc := c.parity.isLt
  rcases Nat.even_or_odd (k + c.parity.val + d.weight.natAbs) with hev | hodd
  · -- the trivial multiplier
    obtain ⟨c', m, C, hC, hm, hpm, hcos⟩ : ∃ (c' : Fin 3) (m : ℕ) (C : ℂ), C ≠ 0 ∧ m ≤ 2 ∧
        m % 2 = (c.parity.val + (d.weight.natAbs + 1) % 2) % 2 ∧ ∀ θ : ℝ,
          1 * (zp hb 2 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) ^ d.weight.natAbs *
            zp hb c' (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) *
            (((blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) 0 0 : ℝ) : ℂ) ^ c.parity.val) +
          1 * (zm hb 2 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) ^ d.weight.natAbs *
            zm hb c' (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) *
            (((blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) 0 0 : ℝ) : ℂ) ^ c.parity.val) =
          C * (Real.cos θ : ℂ) ^ m := by
      rcases Nat.even_or_odd d.weight.natAbs with hw2 | hw2
      · refine ⟨1, c.parity.val + 1, 2 * Complex.I ^ d.weight.natAbs,
          mul_ne_zero two_ne_zero (hI _), by omega, ?_, fun θ => ?_⟩
        · rw [Nat.even_iff] at hw2
          omega
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hrot θ
          simp only [h1, h2, h3, h4, h5]
          rw [hw2.neg_pow]
          ring
      · refine ⟨2, c.parity.val, 2 * Complex.I ^ (d.weight.natAbs + 1),
          mul_ne_zero two_ne_zero (hI _), by omega, ?_, fun θ => ?_⟩
        · rw [Nat.odd_iff] at hw2
          omega
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hrot θ
          simp only [h1, h2, h5]
          rw [hw2.neg_pow]
          ring
    refine exists_of_flat_test (τ := fun i => realPositionExponent
        [RealBlock.character c, RealBlock.induced d] i)
      (μ := fun _ : ℤ => (1 : ℂ))
      (e := ![c.parity, ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩, 0]) hN hb hr hτ hpar
      (fun _ _ _ => ⟨rfl, rfl⟩) (isSymmetric_one _) ?_ ?_ ?_ hk hτr ?_ (hFc c') (hFt c') (hq c')
      hs (hwin c') hN0 (hAB c') hC hm hpm hcos
    · intro i h1 h2
      fin_cases i
      · show (-1 : ℂ) ^ c.parity.val = _
        exact hc0.symm
      · exact absurd rfl h1
      · exact absurd rfl h2
    · show (-1 : ℂ) ^ ((d.weight.natAbs + 1) % 2) = _
      rw [hc1, ← neg_one_pow_eq_pow_mod_two, mul_one]
    · show (-1 : ℂ) ^ 0 =
        realPositionCharacter [RealBlock.character c, RealBlock.induced d] 2 (-1) * 1
      rw [hc2]
      ring
    · show Odd (k + c.parity.val + (d.weight.natAbs + 1) % 2)
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at hev
      omega
  · -- the sign multiplier: the signs at the block are flipped
    have s1 : Int.sign ((d.weight.natAbs : ℤ) + 1) = 1 := Int.sign_eq_one_of_pos (by omega)
    have s2 : Int.sign (-((d.weight.natAbs : ℤ) + 1)) = -1 :=
      Int.sign_eq_neg_one_of_neg (by omega)
    obtain ⟨c', m, C, hC, hm, hpm, hcos⟩ : ∃ (c' : Fin 3) (m : ℕ) (C : ℂ), C ≠ 0 ∧ m ≤ 2 ∧
        m % 2 = (c.parity.val + d.weight.natAbs % 2) % 2 ∧ ∀ θ : ℝ,
          ((Int.sign ((d.weight.natAbs : ℤ) + 1) : ℤ) : ℂ) *
            (zp hb 2 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) ^ d.weight.natAbs *
            zp hb c' (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) *
            (((blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) 0 0 : ℝ) : ℂ) ^ c.parity.val) +
          ((Int.sign (-((d.weight.natAbs : ℤ) + 1)) : ℤ) : ℂ) *
            (zm hb 2 (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) ^ d.weight.natAbs *
            zm hb c' (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) *
            (((blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) 0 0 : ℝ) : ℂ) ^ c.parity.val) =
          C * (Real.cos θ : ℂ) ^ m := by
      rcases Nat.even_or_odd d.weight.natAbs with hw2 | hw2
      · refine ⟨2, c.parity.val, 2 * Complex.I ^ (d.weight.natAbs + 1),
          mul_ne_zero two_ne_zero (hI _), by omega, ?_, fun θ => ?_⟩
        · rw [Nat.even_iff] at hw2
          omega
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hrot θ
          simp only [h1, h2, h5, s1, s2]
          rw [hw2.neg_pow]
          push_cast
          ring
      · refine ⟨1, c.parity.val + 1, 2 * Complex.I ^ d.weight.natAbs,
          mul_ne_zero two_ne_zero (hI _), by omega, ?_, fun θ => ?_⟩
        · rw [Nat.odd_iff] at hw2
          omega
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hrot θ
          simp only [h1, h2, h3, h4, h5, s1, s2]
          rw [hw2.neg_pow]
          push_cast
          ring
    refine exists_of_flat_test (τ := fun i => realPositionExponent
        [RealBlock.character c, RealBlock.induced d] i)
      (μ := fun j : ℤ => ((Int.sign j : ℤ) : ℂ))
      (e := ![c.parity, ⟨d.weight.natAbs % 2, Nat.mod_lt _ two_pos⟩, 1]) hN hb hr hτ hpar
      (flat_sign hb hpar (w := d.weight.natAbs) ⟨0, by ring⟩
        (fun f j hj => (Submodule.mem_inf.mp f.2).1.2 1 d rfl j
          (by rwa [Int.abs_eq_natAbs d.weight]) 1) hδ)
      (isSymmetric_sign _) ?_ ?_ ?_ hk hτr ?_ (hFc c') (hFt c') (hq c') hs (hwin c') hN0
      (hAB c') hC hm hpm hcos
    · intro i h1 h2
      fin_cases i
      · show (-1 : ℂ) ^ c.parity.val = _
        exact hc0.symm
      · exact absurd rfl h1
      · exact absurd rfl h2
    · show (-1 : ℂ) ^ (d.weight.natAbs % 2) = _
      rw [hc1, ← neg_one_pow_eq_pow_mod_two, pow_succ]
      ring
    · show (-1 : ℂ) ^ 1 =
        realPositionCharacter [RealBlock.character c, RealBlock.induced d] 2 (-1) * -1
      rw [hc2]
      ring
    · show Odd (k + c.parity.val + d.weight.natAbs % 2)
      rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hodd
      omega

/-- The linking of two induction blocks `d`, `e` with `Re t(e) ≤ Re t(d)`:
`t(d) - t(e) = ||m| - |m'||/2 + k` with `k ≥ 1`. -/
theorem linked_induced_induced {d e : ComplexCharacterData}
    (hwd : d.weight ≠ 0) (hwe : e.weight ≠ 0)
    (hexp : realBlockExponent (RealBlock.induced e) ≤ realBlockExponent (RealBlock.induced d))
    (hun : ¬ AreRealBlocksUnlinked (RealBlock.induced d) (RealBlock.induced e)) :
    ∃ k : ℕ, 0 < k ∧ d.exponent - e.exponent =
      ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℕ) : ℂ) / 2 + k := by
  have h : MoeglinDatum.IsLinked (.discrete d.weight.natAbs d.exponent)
      (.discrete e.weight.natAbs e.exponent) := by
    by_contra h
    exact hun fun a ha b hb => by
      simp only [realBlockMoeglinData, hwd, hwe, ↓reduceIte, List.mem_singleton] at ha hb
      subst ha hb
      exact h
  obtain ⟨k, hk, h | h⟩ := h
  · exact ⟨k, hk, h⟩
  · exfalso
    have h' : e.exponent - d.exponent =
        ((((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℕ) : ℝ) / 2 + k : ℝ) : ℂ) := by
      rw [h]
      push_cast
      ring
    have h1 := congrArg Complex.re h'
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    simp only [realBlockExponent] at hexp
    have h2 : (0 : ℝ) < k := by exact_mod_cast hk
    have h3 : (0 : ℝ) ≤ ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith

theorem natAbs_sub_cast (a b : ℕ) :
    ((((a : ℤ) - b).natAbs : ℕ) : ℂ) = (a : ℂ) + b - 2 * ((min a b : ℕ) : ℂ) := by
  have h : ((a : ℤ) - b).natAbs + 2 * min a b = a + b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right h]
      omega
  have h' := congrArg (Nat.cast : ℕ → ℂ) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h'
  linear_combination h'

/-- **Two separated linked induction blocks.** If `t(d) - t(e) = ||m| - |m'||/2 + k` with
`k > min(|m|, |m'|)`, the position exponents satisfy `τ_1 - τ_2 = k - min(|m|, |m'|) > 0`
across the two blocks, and the flat engine at the first block applies at `r = 1`. -/
theorem separatedInducedInducedLinkedJacquetFunctional {d e : ComplexCharacterData} {k : ℕ}
    (hk : min d.weight.natAbs e.weight.natAbs < k)
    (hlink : d.exponent - e.exponent =
      ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℕ) : ℂ) / 2 + k) :
    RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e] := by
  have hN : realRank [RealBlock.induced d, RealBlock.induced e] = 4 := rfl
  have hb : 0 + 1 < 4 := by norm_num
  have hb2 : 2 + 1 < 4 := by norm_num
  have hr : 1 + 1 < 4 := by norm_num
  have hτ := fun (i : Fin 4) (x : ℝ) =>
    realPositionCharacter_exp [RealBlock.induced d, RealBlock.induced e] i x
  have hc0 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) := realInducedFirstCharacter_neg_one d
  have hc1 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) = 1 :=
    realInducedSecondCharacter_neg_one d
  have hc2 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 2 (-1) =
      (-1 : ℂ) ^ (e.weight.natAbs + 1) := realInducedFirstCharacter_neg_one e
  have hc3 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 3 (-1) = 1 :=
    realInducedSecondCharacter_neg_one e
  have hpar : (-1 : ℂ) ^ ((d.weight.natAbs : ℤ) + 1) =
      realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) := by
    rw [hc0, hc1, mul_one, ← zpow_natCast]
    push_cast
    rfl
  obtain ⟨K, hK0, hKk⟩ : ∃ K : ℕ, 0 < K ∧ K + min d.weight.natAbs e.weight.natAbs = k :=
    ⟨k - min d.weight.natAbs e.weight.natAbs, by omega, by omega⟩
  have hτr : realPositionExponent [RealBlock.induced d, RealBlock.induced e]
        ((ia hr : Fin 4) : ℕ) -
      realPositionExponent [RealBlock.induced d, RealBlock.induced e]
        ((ib hr : Fin 4) : ℕ) = K := by
    show (d.exponent - (d.weight.natAbs : ℂ) / 2) - (e.exponent + (e.weight.natAbs : ℂ) / 2) = K
    have hKk' : (K : ℂ) + ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) = k := by
      exact_mod_cast hKk
    linear_combination hlink + (1 / 2 : ℂ) * natAbs_sub_cast d.weight.natAbs e.weight.natAbs -
      hKk'
  -- the test functions
  have hFc : ∀ c' c'' : Fin 4, Continuous fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
      bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ := fun c' c'' =>
    (continuous_bf hb 0 c' _).mul (continuous_bf hb2 3 c'' _)
  have hFt : ∀ c' c'' : Fin 4, IsTranslateFinite
      (id : Matrix.unitaryGroup (Fin 4) ℝ → Matrix.unitaryGroup (Fin 4) ℝ)
      (fun κ => (fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ)
          (κ : Matrix (Fin 4) (Fin 4) ℝ)) := fun c' c'' =>
    isTranslateFinite_mul (isTranslateFinite_bf hb 0 c' _) (isTranslateFinite_bf hb2 3 c'' _)
  have hq : ∀ c' c'' : Fin 4, IsSignEq
      (Pi.single (ia hb) (d.weight.natAbs + 1) + Pi.single (ia hb2) (e.weight.natAbs + 1))
      (fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ) := fun c' c'' =>
    isSignEq_mul (isSignEq_bf hb 0 c' _) (isSignEq_bf hb2 3 c'' _)
  have hs : ∀ i : Fin 4, (-1 : ℂ) ^
      ((Pi.single (ia hb) (d.weight.natAbs + 1) + Pi.single (ia hb2) (e.weight.natAbs + 1) :
        Fin 4 → ℕ) i) =
      realPositionCharacter [RealBlock.induced d, RealBlock.induced e] i (-1) := by
    intro i
    fin_cases i
    · simp [ia, hc0]
    · simp [ia, hc1]
    · simp [ia, hc2]
    · simp [ia, hc3]
  have hAB : ∀ (c' c'' : Fin 4) (φ : ℝ) (κ : Matrix (Fin 4) (Fin 4) ℝ),
      (fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ)
        ((blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * κ) =
      expMode ((d.weight.natAbs : ℤ) + 1) φ *
          (fun κ : Matrix (Fin 4) (Fin 4) ℝ => zp hb 0 κ ^ d.weight.natAbs * zp hb c' κ *
            bf hb2 3 c'' e.weight.natAbs κ) κ +
        expMode (-((d.weight.natAbs : ℤ) + 1)) φ *
          (fun κ : Matrix (Fin 4) (Fin 4) ℝ => zm hb 0 κ ^ d.weight.natAbs * zm hb c' κ *
            bf hb2 3 c'' e.weight.natAbs κ) κ := by
    intro c' c'' φ κ
    dsimp only
    rw [bf_rot, bf_rot_of_disjoint hb2 hb (Or.inr (by norm_num))]
    ring
  have hAB2 : ∀ (c' c'' : Fin 4) (φ : ℝ) (κ : Matrix (Fin 4) (Fin 4) ℝ),
      (fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ)
        ((blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * κ) =
      expMode ((e.weight.natAbs : ℤ) + 1) φ *
          (fun κ : Matrix (Fin 4) (Fin 4) ℝ => bf hb 0 c' d.weight.natAbs κ *
            (zp hb2 3 κ ^ e.weight.natAbs * zp hb2 c'' κ)) κ +
        expMode (-((e.weight.natAbs : ℤ) + 1)) φ *
          (fun κ : Matrix (Fin 4) (Fin 4) ℝ => bf hb 0 c' d.weight.natAbs κ *
            (zm hb2 3 κ ^ e.weight.natAbs * zm hb2 c'' κ)) κ := by
    intro c' c'' φ κ
    dsimp only
    rw [bf_rot_of_disjoint hb hb2 (Or.inl (by norm_num)), bf_rot]
    ring
  have hwin : ∀ (c' c'' : Fin 4) (p : ℕ) (d' : ComplexCharacterData),
      realInducedBlockAt [RealBlock.induced d, RealBlock.induced e] p = some d' →
      ∀ j : ℤ, |j| < |d'.weight| → ∀ κ : Matrix (Fin 4) (Fin 4) ℝ,
        κ ∈ Matrix.unitaryGroup (Fin 4) ℝ →
        coeff j (fun φ => (fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
          bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ)
            ((blockRotation 4 p φ : Matrix (Fin 4) (Fin 4) ℝ) * κ)) = 0 := by
    intro c' c'' p d' hd j hj κ _
    rcases p with _ | _ | _ | _ | p
    · simp only [realInducedBlockAt, Option.some.injEq] at hd
      subst hd
      exact coeff_eq_zero_of_two_mode (F := fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ) (hAB c' c'')
        (abs_lt_natAbs_succ hj) κ
    · simp [realInducedBlockAt] at hd
    · simp only [realInducedBlockAt, Option.some.injEq] at hd
      subst hd
      exact coeff_eq_zero_of_two_mode (F := fun κ : Matrix (Fin 4) (Fin 4) ℝ =>
        bf hb 0 c' d.weight.natAbs κ * bf hb2 3 c'' e.weight.natAbs κ) (hAB2 c' c'')
        (abs_lt_natAbs_succ hj) κ
    · simp [realInducedBlockAt] at hd
    · simp [realInducedBlockAt] at hd
  have hN0 : ((d.weight.natAbs : ℤ) + 1) ≠ 0 := by omega
  have hrot : ∀ θ : ℝ,
      zp hb 0 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = 1 ∧
      zm hb 0 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = 1 ∧
      zp hb 1 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = Complex.I * Real.cos θ ∧
      zm hb 1 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = -(Complex.I * Real.cos θ) ∧
      zp hb2 3 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = Complex.I ∧
      zm hb2 3 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = -Complex.I ∧
      zp hb2 2 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = Real.cos θ ∧
      zm hb2 2 (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) = Real.cos θ := by
    intro θ
    simp only [zp, zm, blockRotation_apply hr]
    simp [ia, ib]
  have hI : ∀ p : ℕ, Complex.I ^ p ≠ 0 := fun p => pow_ne_zero _ Complex.I_ne_zero
  -- the second block at `r_1(θ)`
  obtain ⟨c'', m2, C2, hC2, hm2, hpm2, hcos2⟩ : ∃ (c'' : Fin 4) (m2 : ℕ) (C2 : ℂ), C2 ≠ 0 ∧
      m2 ≤ 1 ∧ m2 % 2 = (e.weight.natAbs + 1) % 2 ∧ ∀ θ : ℝ,
        bf hb2 3 c'' e.weight.natAbs (blockRotation 4 1 θ : Matrix (Fin 4) (Fin 4) ℝ) =
          C2 * (Real.cos θ : ℂ) ^ m2 := by
    rcases Nat.even_or_odd e.weight.natAbs with hw2 | hw2
    · refine ⟨2, 1, 2 * Complex.I ^ e.weight.natAbs, mul_ne_zero two_ne_zero (hI _), le_rfl,
        ?_, fun θ => ?_⟩
      · rw [Nat.even_iff] at hw2
        omega
      · obtain ⟨-, -, -, -, h5, h6, h7, h8⟩ := hrot θ
        rw [bf, h5, h6, h7, h8, hw2.neg_pow]
        ring
    · refine ⟨3, 0, 2 * Complex.I ^ (e.weight.natAbs + 1), mul_ne_zero two_ne_zero (hI _),
        zero_le_one, ?_, fun θ => ?_⟩
      · rw [Nat.odd_iff] at hw2
        omega
      · obtain ⟨-, -, -, -, h5, h6, -, -⟩ := hrot θ
        have h := hw2.add_one.neg_pow Complex.I
        rw [pow_succ, pow_succ] at h
        rw [bf, h5, h6, h]
        ring
  rcases Nat.even_or_odd (K + e.weight.natAbs) with hev | hodd
  · -- the trivial multiplier
    refine exists_of_flat_test (τ := fun i => realPositionExponent
        [RealBlock.induced d, RealBlock.induced e] i)
      (μ := fun _ : ℤ => (1 : ℂ))
      (e := ![⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩, 0,
        ⟨(e.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩, 0]) hN hb hr hτ hpar
      (fun _ _ _ => ⟨rfl, rfl⟩) (isSymmetric_one _) ?_ ?_ ?_ hK0 hτr ?_ (hFc 0 c'') (hFt 0 c'')
      (hq 0 c'') hs (hwin 0 c'') hN0 (hAB 0 c'') (C := 2 * C2) (mul_ne_zero two_ne_zero hC2)
      (m := m2) (by omega) ?_ ?_
    · intro i h1 h2
      fin_cases i
      · exact absurd rfl h1
      · exact absurd rfl h2
      · show (-1 : ℂ) ^ ((e.weight.natAbs + 1) % 2) = _
        rw [hc2, ← neg_one_pow_eq_pow_mod_two]
      · show (-1 : ℂ) ^ 0 = _
        rw [hc3]
        ring
    · show (-1 : ℂ) ^ ((d.weight.natAbs + 1) % 2) = _
      rw [hc0, ← neg_one_pow_eq_pow_mod_two, mul_one]
    · show (-1 : ℂ) ^ 0 =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) * 1
      rw [hc1]
      ring
    · show Odd (K + 0 + (e.weight.natAbs + 1) % 2)
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at hev
      omega
    · show m2 % 2 = (0 + (e.weight.natAbs + 1) % 2) % 2
      omega
    · intro θ
      obtain ⟨h1, h2, -⟩ := hrot θ
      simp only [h1, h2, hcos2 θ]
      ring
  · -- the sign multiplier: the signs at the first block are flipped
    have s1 : Int.sign ((d.weight.natAbs : ℤ) + 1) = 1 := Int.sign_eq_one_of_pos (by omega)
    have s2 : Int.sign (-((d.weight.natAbs : ℤ) + 1)) = -1 :=
      Int.sign_eq_neg_one_of_neg (by omega)
    refine exists_of_flat_test (τ := fun i => realPositionExponent
        [RealBlock.induced d, RealBlock.induced e] i)
      (μ := fun j : ℤ => ((Int.sign j : ℤ) : ℂ))
      (e := ![⟨d.weight.natAbs % 2, Nat.mod_lt _ two_pos⟩, 1,
        ⟨(e.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩, 0]) hN hb hr hτ hpar
      (flat_sign hb hpar (w := d.weight.natAbs) ⟨0, by ring⟩
        (fun f j hj => (Submodule.mem_inf.mp f.2).1.2 0 d rfl j
          (by rwa [Int.abs_eq_natAbs d.weight]) 1) ?_)
      (isSymmetric_sign _) ?_ ?_ ?_ hK0 hτr ?_ (hFc 1 c'') (hFt 1 c'') (hq 1 c'') hs
      (hwin 1 c'') hN0 (hAB 1 c'') (C := 2 * Complex.I * C2) (by simp [hC2]) (m := m2 + 1)
      (by omega) ?_ ?_
    · show (realPositionExponent [RealBlock.induced d, RealBlock.induced e] 0 +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) -
        (realPositionExponent [RealBlock.induced d, RealBlock.induced e] 1 +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) = (d.weight.natAbs : ℂ) + 1
      show (d.exponent + (d.weight.natAbs : ℂ) / 2 + (((4 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) -
        (d.exponent - (d.weight.natAbs : ℂ) / 2 + (((4 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) =
          (d.weight.natAbs : ℂ) + 1
      push_cast
      ring
    · intro i h1 h2
      fin_cases i
      · exact absurd rfl h1
      · exact absurd rfl h2
      · show (-1 : ℂ) ^ ((e.weight.natAbs + 1) % 2) = _
        rw [hc2, ← neg_one_pow_eq_pow_mod_two]
      · show (-1 : ℂ) ^ 0 = _
        rw [hc3]
        ring
    · show (-1 : ℂ) ^ (d.weight.natAbs % 2) = _
      rw [hc0, ← neg_one_pow_eq_pow_mod_two, pow_succ]
      ring
    · show (-1 : ℂ) ^ 1 =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) * -1
      rw [hc1]
      ring
    · show Odd (K + 1 + (e.weight.natAbs + 1) % 2)
      rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hodd
      omega
    · show (m2 + 1) % 2 = (1 + (e.weight.natAbs + 1) % 2) % 2
      omega
    · intro θ
      obtain ⟨h1, h2, h3, h4, -⟩ := hrot θ
      simp only [h1, h2, h3, h4, hcos2 θ, s1, s2]
      push_cast
      ring

/-- **Two linked induction blocks**, from the interlaced case: the separated case
`k > min(|m|, |m'|)` is `separatedInducedInducedLinkedJacquetFunctional`. -/
theorem realInducedInducedLinkedJacquetFunctional_of_interlaced
    (hint : RealInterlacedInducedInducedLinkedJacquetFunctionalStatement) :
    RealInducedInducedLinkedJacquetFunctionalStatement := by
  intro d e hwd hwe hexp hun
  obtain ⟨k, hk, hlink⟩ := linked_induced_induced hwd hwe hexp hun
  by_cases hsep : min d.weight.natAbs e.weight.natAbs < k
  · exact separatedInducedInducedLinkedJacquetFunctional hsep hlink
  · exact hint d e k hwd hwe hk (not_lt.mp hsep) hlink

end Pairs

end RealBlockFlatJacquet

end Langlands.Archimedean
