import Langlands.Representation.Archimedean.ComplexJacquetReduction
import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.GroupScheme.Dynamic.UnitaryLeviIntersection
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Jacquet functionals on the diagonal unitary torus

Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module and `ℓ` a nonzero Jacquet functional with exponents
`a`, `b` (`IsComplexJacquetFunctional`). This file shows that the imaginary exponents are
integral, `b_j = i l_j` with `l_j ∈ ℤ`, and that `ℓ` transforms under the diagonal unitary
matrices `m` by the character `m ↦ ∏ⱼ m_jj^{l_j}` (`IsComplexJacquetFunctional.exists_weight`).

Tools:

* `skewExp Y`: the unitary matrix `exp Y` of a skew-Hermitian `Y`, and the derivative of
  `t ↦ μ(ρ(exp(tY)) w)` at every `s` (`hasDerivAt_skewExp`), from the curve clause of
  `IsComplexGKModule` and the group law `exp((s + t)Y) = exp(sY) exp(tY)`;
* the Library lemma `Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt`: the
  solution of `φ' = c φ` on `ℝ`;
* `IsComplexJacquetFunctional.apply_upper`: on an upper triangular `X`,
  `ℓ(π(1 ⊗ X) v) = ∑ⱼ (Re X_jj a_j + Im X_jj b_j) ℓ(v)`;
* `offDiag_eq_zero_of_upper_unitary`: an upper triangular unitary matrix is diagonal, a
  specialization of the Library theorem
  `Langlands.GroupScheme.GeneralLinear.mem_blockLeviSubgroup_of_unitary`.
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

-- As in `GeneralLinear`: the operator norm on matrices needs reduction through the
-- normed-ring instances.
set_option backward.isDefEq.respectTransparency false

universe uV

/-! ## Exponentials of skew-Hermitian matrices -/

section SkewExp

variable {n : ℕ}

theorem star_real_smul_of_skew {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) (t : ℝ) :
    star (t • Y) = -(t • Y) := by
  rw [star_smul, hY, star_trivial, smul_neg]

/-- The unitary matrix `exp Y` of a skew-Hermitian matrix `Y`. -/
def skewExp (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp Y,
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr hY)⟩

@[simp]
theorem coe_skewExp (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y) :
    (skewExp Y hY : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp Y :=
  rfl

theorem skewExp_zero_smul {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) :
    skewExp ((0 : ℝ) • Y) (star_real_smul_of_skew hY 0) = 1 := by
  apply Subtype.ext
  simp

theorem skewExp_add_smul {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) (s t : ℝ) :
    skewExp ((s + t) • Y) (star_real_smul_of_skew hY (s + t)) =
      skewExp (s • Y) (star_real_smul_of_skew hY s) *
        skewExp (t • Y) (star_real_smul_of_skew hY t) := by
  apply Subtype.ext
  change NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)

/-- `t ↦ exp(tY)` has derivative `Y` at `0`. -/
theorem hasDerivAt_exp_smul_zero (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y)) Y 0 := by
  simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)

/-- The entries of a matrix-valued curve with derivative `X` have derivatives `X i j`. -/
theorem hasDerivAt_entry {m : ℕ} {γ : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {X : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : HasDerivAt γ X t) (i j : Fin m) :
    HasDerivAt (fun s => γ s i j) (X i j) t :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    t h

theorem hasDerivAt_skewExp_entry {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y)
    (i j : Fin n) :
    HasDerivAt
      (fun t : ℝ => (skewExp (t • Y) (star_real_smul_of_skew hY t) :
        Matrix (Fin n) (Fin n) ℂ) i j) (Y i j) 0 :=
  hasDerivAt_entry (hasDerivAt_exp_smul_zero Y) i j

end SkewExp

/-! ## Derivatives along one-parameter subgroups -/

section Curves

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- Along the one-parameter subgroup `t ↦ exp(tY)` of a skew-Hermitian `Y`, the function
`t ↦ μ(ρ(exp(tY)) w)` has derivative `μ(ρ(exp(sY)) π(1 ⊗ Y) w)` at every `s`. -/
theorem hasDerivAt_skewExp (hgk : IsComplexGKModule n ρ π) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : star Y = -Y) (μ : V →ₗ[ℂ] ℂ) (w : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => μ (ρ (skewExp (t • Y) (star_real_smul_of_skew hY t)) w))
      (μ (ρ (skewExp (s • Y) (star_real_smul_of_skew hY s)) (π (1 ⊗ₜ Y) w))) s := by
  set k : ℝ → Matrix.unitaryGroup (Fin n) ℂ :=
    fun t => skewExp (t • Y) (star_real_smul_of_skew hY t) with hk
  have h0 := hgk.2.2.1 k Y (skewExp_zero_smul hY) (hasDerivAt_skewExp_entry hY) w
    (μ ∘ₗ ρ (k s))
  have h1 : HasDerivAt (fun t => (μ ∘ₗ ρ (k s)) (ρ (k t) w))
      ((μ ∘ₗ ρ (k s)) (π (1 ⊗ₜ Y) w)) (s - s) := by
    rw [sub_self]
    exact h0
  have h2 := h1.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change μ (ρ (k t) w) = μ (ρ (k s) (ρ (k (t - s)) w))
  rw [← Module.End.mul_apply, ← map_mul, hk, ← skewExp_add_smul hY, add_sub_cancel]

end Curves

/-! ## Jacquet functionals on upper triangular directions -/

section Upper

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

theorem one_tmul_real_smul (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (1 : ℂ) ⊗ₜ[ℝ] (r • M) = (r : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] M) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Complex.real_smul, smul_eq_mul]

/-- `π(1 ⊗ rM) = r π(1 ⊗ M)` for real `r`. -/
theorem lie_one_tmul_real_smul (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (v : V) :
    π (1 ⊗ₜ (r • M)) v = (r : ℂ) • π (1 ⊗ₜ M) v := by
  rw [one_tmul_real_smul, map_smul, LinearMap.smul_apply]

theorem lie_one_tmul_add (M M' : Matrix (Fin n) (Fin n) ℂ) (v : V) :
    π (1 ⊗ₜ (M + M')) v = π (1 ⊗ₜ M) v + π (1 ⊗ₜ M') v := by
  rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply]

theorem lie_one_tmul_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (v : V) : π (1 ⊗ₜ (∑ i ∈ s, M i)) v = ∑ i ∈ s, π (1 ⊗ₜ M i) v := by
  rw [TensorProduct.tmul_sum, map_sum, LinearMap.sum_apply]

/-- `M_jj = Re M_jj E_jj + Im M_jj (i E_jj)` at a diagonal position. -/
theorem single_eq_re_add_im (j : Fin n) (z : ℂ) :
    Matrix.single j j z = z.re • Matrix.single j j 1 + z.im • Matrix.single j j Complex.I := by
  rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
  congr 1
  rw [Complex.real_smul, Complex.real_smul, mul_one]
  exact (Complex.re_add_im z).symm

/-- A Jacquet functional on an upper triangular direction:
`ℓ(π(1 ⊗ X) v) = ∑ⱼ (Re X_jj a_j + Im X_jj b_j) ℓ(v)`. -/
theorem IsComplexJacquetFunctional.apply_upper {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ}
    (hJ : IsComplexJacquetFunctional n π ℓ a b) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsUpperTriangular) (v : V) :
    ℓ (π (1 ⊗ₜ X) v) = (∑ j, (((X j j).re : ℂ) * a j + ((X j j).im : ℂ) * b j)) * ℓ v := by
  classical
  set D : Matrix (Fin n) (Fin n) ℂ := ∑ j, Matrix.single j j (X j j) with hD
  have hDapp : ∀ i j, D i j = if i = j then X i i else 0 := by
    intro i j
    rw [hD, Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [hij, ↓reduceIte]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [ite_eq_right_iff]
      rintro ⟨⟨rfl, rfl⟩, rfl⟩
      exact absurd rfl hij
  have hN : ∀ i j : Fin n, (j : ℕ) ≤ i → (X - D) i j = 0 := by
    intro i j hji
    rw [Matrix.sub_apply, hDapp]
    rcases (Nat.lt_or_eq_of_le hji) with h | h
    · have hlt : j < i := h
      rw [hX hlt, ite_eq_right_iff.mpr (fun h => absurd h (ne_of_gt hlt)), sub_zero]
    · have he : j = i := Fin.ext h
      subst he
      simp
  have hsplit : π (1 ⊗ₜ X) v = π (1 ⊗ₜ (X - D)) v + π (1 ⊗ₜ D) v := by
    rw [← lie_one_tmul_add, sub_add_cancel]
  rw [hsplit, map_add, hJ.1 _ hN, zero_add, hD, lie_one_tmul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [single_eq_re_add_im, lie_one_tmul_add, lie_one_tmul_real_smul, lie_one_tmul_real_smul,
    map_add, map_smul, map_smul, (hJ.2 j v).1, (hJ.2 j v).2, smul_eq_mul, smul_eq_mul]
  ring

end Upper

/-! ## Upper triangular unitary matrices -/

/-- An upper triangular unitary matrix is diagonal. This specializes the Library theorem
`Langlands.GroupScheme.GeneralLinear.mem_blockLeviSubgroup_of_unitary` (a unitary matrix in a
weight-block parabolic subgroup lies in its Levi subgroup) to the decreasing weights
`e i = -i`: for these weights the block parabolic subgroup is the upper triangular group and
its Levi subgroup is the diagonal group. -/
theorem offDiag_eq_zero_of_upper_unitary {n : ℕ} {m : Matrix (Fin n) (Fin n) ℂ}
    (hm : m ∈ Matrix.unitaryGroup (Fin n) ℂ) (hu : m.IsUpperTriangular) :
    ∀ i j, i ≠ j → m i j = 0 := by
  let g : GL (Fin n) ℂ := Unitary.toUnits ⟨m, hm⟩
  let e : Fin n → ℤ := fun i => -(i.val : ℤ)
  have hp : g ∈ Langlands.GroupScheme.GeneralLinear.blockParabolicSubgroup ℂ e := by
    apply (Langlands.GroupScheme.GeneralLinear.mem_blockParabolicSubgroup ℂ e).mpr
    intro i j hij
    change -(i.val : ℤ) < -(j.val : ℤ) at hij
    have hji : j.val < i.val := by omega
    exact hu hji
  have hd := Langlands.GroupScheme.GeneralLinear.mem_blockLeviSubgroup_of_unitary e hp hm
  intro i j hij
  apply hd i j
  change -(i.val : ℤ) ≠ -(j.val : ℤ)
  intro heq
  apply hij
  apply Fin.ext
  omega

/-! ## The diagonal unitary torus -/

section Torus

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- The skew-Hermitian diagonal matrix `diag(i θ_j)`. -/
def diagI (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => (θ j : ℂ) * Complex.I

theorem star_diagI (θ : Fin n → ℝ) : star (diagI θ) = -diagI θ := by
  rw [Matrix.star_eq_conjTranspose, diagI, Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext j
  simp

theorem exp_diagI (θ : Fin n → ℝ) :
    NormedSpace.exp (diagI θ) =
      Matrix.diagonal fun j => Complex.exp ((θ j : ℂ) * Complex.I) := by
  rw [diagI, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

/-- On the torus element `exp(diag(i θ))`, a Jacquet functional picks up the factor
`exp(∑ⱼ θ_j b_j)`. -/
theorem IsComplexJacquetFunctional.apply_skewExp_diagI (hgk : IsComplexGKModule n ρ π)
    {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ} (hJ : IsComplexJacquetFunctional n π ℓ a b)
    (θ : Fin n → ℝ) (w : V) :
    ℓ (ρ (skewExp (diagI θ) (star_diagI θ)) w) =
      Complex.exp (∑ j, (θ j : ℂ) * b j) * ℓ w := by
  set Y : Matrix (Fin n) (Fin n) ℂ := diagI θ with hYdef
  have hY : star Y = -Y := star_diagI θ
  set c : ℂ := ∑ j, (θ j : ℂ) * b j with hc
  have hYup : Y.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hYc : ∀ v : V, ℓ (π (1 ⊗ₜ Y) v) = c * ℓ v := by
    intro v
    rw [hJ.apply_upper Y hYup v, hc]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hYdef, diagI]
  set φ : ℝ → ℂ := fun t => ℓ (ρ (skewExp (t • Y) (star_real_smul_of_skew hY t)) w) with hφ
  have hderiv : ∀ s, HasDerivAt φ (c * φ s) s := by
    intro s
    have h := hasDerivAt_skewExp hgk hY ℓ w s
    convert h using 1
    set k := skewExp (s • Y) (star_real_smul_of_skew hY s) with hk
    have hcomm : (k : Matrix (Fin n) (Fin n) ℂ) * Y * (star k : Matrix (Fin n) (Fin n) ℂ) = Y := by
      have h1 : Commute Y (k : Matrix (Fin n) (Fin n) ℂ) := by
        rw [hk, coe_skewExp]
        exact ((Commute.refl Y).smul_right s).exp_right
      rw [← h1.eq, mul_assoc, Unitary.mul_star_self_of_mem k.2, mul_one]
    rw [hgk.2.2.2, hcomm, hYc]
  have h1 := Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt hderiv 1
  have hk1 : skewExp ((1 : ℝ) • Y) (star_real_smul_of_skew hY 1) = skewExp Y hY :=
    Subtype.ext (by simp)
  have hφ0 : φ 0 = ℓ w := by
    simp only [hφ, skewExp_zero_smul hY, map_one, Module.End.one_apply]
  rw [hφ0] at h1
  simp only [hφ, hk1, Complex.ofReal_one, mul_one] at h1
  exact h1

/-- The imaginary exponents of a nonzero Jacquet functional are integral: `b_j = i l_j`. -/
theorem IsComplexJacquetFunctional.exists_int (hgk : IsComplexGKModule n ρ π)
    {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ} (hJ : IsComplexJacquetFunctional n π ℓ a b)
    (hℓ : ℓ ≠ 0) : ∃ l : Fin n → ℤ, ∀ j, b j = Complex.I * (l j : ℂ) := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, ℓ w ≠ 0 := by
    by_contra h
    exact hℓ (LinearMap.ext fun v => by simpa using not_not.mp (not_exists.mp h v))
  have key : ∀ j, ∃ l : ℤ, b j = Complex.I * (l : ℂ) := by
    intro j
    set θ : Fin n → ℝ := Pi.single j (2 * Real.pi) with hθ
    have h1 := hJ.apply_skewExp_diagI hgk θ w
    have hk : skewExp (diagI θ) (star_diagI θ) = 1 := by
      apply Subtype.ext
      rw [coe_skewExp, exp_diagI]
      show _ = (1 : Matrix (Fin n) (Fin n) ℂ)
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases hi : i = j
      · subst hi
        simp only [hθ, Pi.single_eq_same]
        push_cast
        exact Complex.exp_two_pi_mul_I
      · simp [hθ, hi]
    rw [hk, map_one, Module.End.one_apply] at h1
    have hsum : ∑ i, (θ i : ℂ) * b i = 2 * Real.pi * b j := by
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [hθ, hi]) (by simp)]
      simp [hθ]
    have hexp : Complex.exp (2 * Real.pi * b j) = 1 := by
      rw [← hsum]
      have h2 : Complex.exp (∑ i, (θ i : ℂ) * b i) * ℓ w = 1 * ℓ w := by
        rw [one_mul]
        exact h1.symm
      exact mul_right_cancel₀ hw h2
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨m, ?_⟩
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    apply mul_left_cancel₀ hpi
    linear_combination hm
  choose l hl using key
  exact ⟨l, hl⟩

/-- A diagonal unitary matrix has entries of norm one on the diagonal. -/
theorem norm_diag_eq_one_of_unitary {m : Matrix (Fin n) (Fin n) ℂ}
    (hmu : m ∈ Matrix.unitaryGroup (Fin n) ℂ) (hm : ∀ i j, i ≠ j → m i j = 0) (j : Fin n) :
    ‖m j j‖ = 1 := by
  have hsm : star m * m = 1 := Unitary.star_mul_self_of_mem hmu
  have h := congrFun (congrFun hsm j) j
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [hm k j hk, mul_zero])
    (by simp), Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def, Complex.conj_mul'] at h
  have h2 : ‖m j j‖ ^ 2 = 1 := by exact_mod_cast h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

/-- **The torus character of a Jacquet functional.** The imaginary exponents are integral,
`b_j = i l_j`, and a diagonal unitary matrix `m` acts on `ℓ` by `∏ⱼ m_jj^{l_j}`. -/
theorem IsComplexJacquetFunctional.exists_weight (hgk : IsComplexGKModule n ρ π)
    {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ} (hJ : IsComplexJacquetFunctional n π ℓ a b)
    (hℓ : ℓ ≠ 0) :
    ∃ l : Fin n → ℤ, (∀ j, b j = Complex.I * (l j : ℂ)) ∧
      ∀ m : Matrix.unitaryGroup (Fin n) ℂ,
        (∀ i j, i ≠ j → (m : Matrix (Fin n) (Fin n) ℂ) i j = 0) → ∀ w : V,
          ℓ (ρ m w) = (∏ j, ((m : Matrix (Fin n) (Fin n) ℂ) j j) ^ (l j)) * ℓ w := by
  obtain ⟨l, hl⟩ := hJ.exists_int hgk hℓ
  refine ⟨l, hl, fun m hm w => ?_⟩
  set θ : Fin n → ℝ := fun j => Complex.arg ((m : Matrix (Fin n) (Fin n) ℂ) j j) with hθ
  have hentry : ∀ j, (m : Matrix (Fin n) (Fin n) ℂ) j j = Complex.exp ((θ j : ℂ) * Complex.I) := by
    intro j
    have h := Complex.norm_mul_exp_arg_mul_I ((m : Matrix (Fin n) (Fin n) ℂ) j j)
    rw [norm_diag_eq_one_of_unitary m.2 hm j, Complex.ofReal_one, one_mul] at h
    exact h.symm
  have hmθ : m = skewExp (diagI θ) (star_diagI θ) := by
    apply Subtype.ext
    rw [coe_skewExp, exp_diagI]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hentry]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hm i j hij
  have h := hJ.apply_skewExp_diagI hgk θ w
  rw [← hmθ] at h
  rw [h, Complex.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hentry, hl j, ← Complex.exp_int_mul]
  congr 1
  ring

end Torus

end Langlands.Archimedean
