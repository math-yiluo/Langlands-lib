import Langlands.Representation.Archimedean.ComplexSwapJacquetAnalysis
import Langlands.Representation.Archimedean.ComplexSwapJacquetDecay
import Langlands.Representation.Archimedean.ComplexJacquetReduction

/-!
# The rank-one Jacquet functional of a complex principal series

Fix `ds`, adjacent positions `i` and `j = i + 1`, and `c ∈ ℂ`. On the `U(n)`-finite vectors
`v` of the standard module of `ds`, put `g_c(v) = R(c E_jj) v - κ_j(c) v` (`shift`) and
`Λ_c(v) = ∫_ℂ g_c(v)(s x(z)) dz` (`functional`), where `s x(z) = chart z`.

This file shows that `Λ_c` is a Jacquet functional whose exponents at `i` and `j` are those of
`ds` with the characters at `i` and `j` swapped (`isComplexJacquetFunctional_functional`). It
assumes two packages of facts about the chart:

* `ChartLieFacts`: pointwise formulas for `R(X) f (s x(z))` and `R(X) f (1)`;
* `ChartDecay`: the decay bounds `|h(s x(z))| ≤ C (1 + |z|)⁻¹`, improved to
  `C (1 + |z|)⁻³` when `h(1) = 0`. They hold when `Re(t_i - t_j) ≥ 0` (`chartDecay`).

`exists_swapJacquetFunctional` specializes the result to `ds = pre ++ d :: e :: post` and the
exponents of `pre ++ e :: d :: post`.

Proof outline. `g_c(v)(1) = 0`, so `z ↦ g_c(v)(s x(z))` is integrable and `Λ_c` is linear.

* Strictly upper triangular `X`: `[R(c E_jj), R(X)] = R([c E_jj, X])` gives
  `g_c(R(X) v) = R(X) g_c(v) + R([c E_jj, X]) v` with `[c E_jj, X]` strictly upper. For `h` in
  the principal series and `Y` strictly upper, `R(Y) h (s x(z)) = Dφ_h(z)(Y_ij)` with
  `φ_h(z) = h(s x(z))`, whose integral vanishes by `integral_fderiv_one_eq_zero` and
  `integral_fderiv_I_eq_zero`.
* Diagonal directions `c' E_kk`: they commute with `c E_jj`, so
  `g_c(R(c' E_kk) v) = R(c' E_kk) g`, `g = g_c(v)`. For `k ∉ {i, j}` this is `κ_k(c') g`; for
  `k = j` it is `κ_i(c') φ_g(z) + Dφ_g(z)(c' z)` and for `k = i` it is
  `κ_j(c') φ_g(z) - Dφ_g(z)(c' z)`. Euler's identity `∫ Dφ(z) z = -2 ∫ φ` and
  `∫ Dφ(z)(i z) = 0` finish the computation.
-/

noncomputable section

open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator

open MeasureTheory Filter Topology

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-- The `U(n)`-finite functions of the standard module of `ds`. -/
abbrev KFs (n : ℕ) (ds : List ComplexCharacterData) :
    Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

/-- Pointwise formulas for right derivatives along the chart `s x(z)` and at `1`, for
functions `f` in the standard module of `ds`; `φ(z) = f(s x(z))`. -/
structure ChartLieFacts (ds : List ComplexCharacterData) (hn : ds.length = n) (i j : Fin n)
    (hj : (j : ℕ) = i + 1) : Prop where
  /-- `R(w E_ij) f (s x(z)) = Dφ(z)(w)`. -/
  single_ij : ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n ds →
    ∀ w z : ℂ, rightDerivative (matrixModel ℂ n) (Matrix.single i j w) f (chart i j hj z) =
      fderiv ℝ (fun z => f (chart i j hj z)) z w
  /-- `R(X) f (s x(z)) = 0` for `X` strictly upper triangular with `X_ij = 0`. -/
  strictUpper : ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n ds →
    ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ a b : Fin n, b ≤ a → X a b = 0) → X i j = 0 →
      ∀ z : ℂ, rightDerivative (matrixModel ℂ n) X f (chart i j hj z) = 0
  /-- `R(c E_kk) f (s x(z)) = κ_k(c) f(s x(z))` for `k ∉ {i, j}`. -/
  diag_other : ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n ds →
    ∀ k : Fin n, k ≠ i → k ≠ j → ∀ c z : ℂ,
      rightDerivative (matrixModel ℂ n) (Matrix.single k k c) f (chart i j hj z) =
        kappa ds hn k c * f (chart i j hj z)
  /-- `R(c E_jj) f (s x(z)) = κ_i(c) f(s x(z)) + Dφ(z)(c z)`. -/
  diag_j : ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n ds →
    ∀ c z : ℂ, rightDerivative (matrixModel ℂ n) (Matrix.single j j c) f (chart i j hj z) =
      kappa ds hn i c * f (chart i j hj z) + fderiv ℝ (fun z => f (chart i j hj z)) z (c * z)
  /-- `R(c E_ii) f (s x(z)) = κ_j(c) f(s x(z)) - Dφ(z)(c z)`. -/
  diag_i : ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n ds →
    ∀ c z : ℂ, rightDerivative (matrixModel ℂ n) (Matrix.single i i c) f (chart i j hj z) =
      kappa ds hn j c * f (chart i j hj z) - fderiv ℝ (fun z => f (chart i j hj z)) z (c * z)
  /-- `R(X) f (1) = 0` for `X` strictly upper triangular. -/
  one_strictUpper : ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n ds →
    ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ a b : Fin n, b ≤ a → X a b = 0) →
      rightDerivative (matrixModel ℂ n) X f 1 = 0
  /-- `R(c E_kk) f (1) = κ_k(c) f(1)`. -/
  one_diag : ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n ds →
    ∀ (k : Fin n) (c : ℂ),
      rightDerivative (matrixModel ℂ n) (Matrix.single k k c) f 1 = kappa ds hn k c * f 1

/-- Decay of the functions of the standard module of `ds` along the chart:
`|h(s x(z))| ≤ C (1 + |z|)⁻¹`, and `≤ C (1 + |z|)⁻³` when `h(1) = 0`. -/
def ChartDecay (ds : List ComplexCharacterData) (i j : Fin n) (hj : (j : ℕ) = i + 1) : Prop :=
  ∀ h : Langlands.GeneralLinear n ℂ → ℂ, h ∈ complexStandardModule n ds →
    (∃ C, ∀ z, ‖h (chart i j hj z)‖ ≤ C * (1 + ‖z‖)⁻¹) ∧
      (h 1 = 0 → ∃ C, ∀ z, ‖h (chart i j hj z)‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹)

/-- The decay holds for `ds = pre ++ d :: e :: post` at the positions of `d` and `e` when
`Re(t_d - t_e) ≥ 0`. -/
theorem chartDecay (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
    (i j : Fin n) (hi : (i : ℕ) = pre.length) (hj : (j : ℕ) = i + 1)
    (hre : 0 ≤ (d.exponent - e.exponent).re) :
    ChartDecay (pre ++ d :: e :: post) i j hj := fun _ hh =>
  ⟨exists_bound_chart pre post d e i j hi hj hre hh,
    exists_bound_chart_of_eq_zero pre post d e i j hi hj hre hh⟩

/-! ## Generalities -/

theorem mem_of_mem_kFs {ds : List ComplexCharacterData} {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ KFs n ds) : f ∈ complexStandardModule n ds :=
  (Submodule.mem_inf.mp hf).1

theorem coe_lie {ds : List ComplexCharacterData} (X : Matrix (Fin n) (Fin n) ℂ)
    (v : KFs n ds) :
    ((complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) v : KFs n ds) :
        Langlands.GeneralLinear n ℂ → ℂ) =
      rightDerivative (matrixModel ℂ n) X v :=
  principalSeriesLie_one_tmul_apply_coe ℂ n _ X v

theorem rightDerivative_add (X Y : Matrix (Fin n) (Fin n) ℂ)
    (f : Langlands.GeneralLinear n ℂ → ℂ) (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) (X + Y) f g =
      rightDerivative (matrixModel ℂ n) X f g + rightDerivative (matrixModel ℂ n) Y f g := by
  unfold rightDerivative
  exact map_add _ X Y

/-- `[π(1 ⊗ A), π(1 ⊗ X)] = π(1 ⊗ (A X - X A))`, applied to a vector. -/
theorem lie_comm {ds : List ComplexCharacterData} (A X : Matrix (Fin n) (Fin n) ℂ)
    (v : KFs n ds) :
    complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] A) (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) v) =
      complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] A) v) +
        complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] (A * X - X * A)) v := by
  have h := LieHom.map_lie (complexStandardLie n ds) ((1 : ℂ) ⊗ₜ[ℝ] A) ((1 : ℂ) ⊗ₜ[ℝ] X)
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, Ring.lie_def] at h
  rw [h, LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply]
  abel

/-- A real-linear map on `ℂ` is determined by its values at `1` and `i`. -/
theorem clm_apply_eq (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem strictUpper_single {i j : Fin n} (hj : (j : ℕ) = i + 1) (w : ℂ) :
    ∀ a b : Fin n, b ≤ a → Matrix.single i j w a b = 0 := by
  intro a b hab
  apply Matrix.single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  have : (j : ℕ) ≤ i := hab
  omega

theorem strictUpper_sub_single {i j : Fin n} (hj : (j : ℕ) = i + 1)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : ∀ a b : Fin n, b ≤ a → X a b = 0) :
    ∀ a b : Fin n, b ≤ a → (X - Matrix.single i j (X i j)) a b = 0 := by
  intro a b hab
  rw [Matrix.sub_apply, hX a b hab, strictUpper_single hj _ a b hab, sub_zero]

theorem single_commute (j k : Fin n) (c c' : ℂ) :
    Matrix.single j j c * Matrix.single k k c' - Matrix.single k k c' * Matrix.single j j c =
      0 := by
  by_cases hk : k = j
  · rw [hk, Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_comm, sub_self]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hk), Matrix.single_mul_single_of_ne _ _ _ _ hk,
      sub_zero]

theorem le_add_bound {x C₁ C₂ : ℝ} {y : ℝ} (hy : y ≤ C₁ * x) (hx : 0 ≤ x) (hC₂ : 0 ≤ C₂) :
    y ≤ (C₁ + C₂) * x := by
  nlinarith

/-! ## Integrals along the chart -/

section Generic

variable {ds : List ComplexCharacterData} {hn : ds.length = n} {i j : Fin n}
  {hj : (j : ℕ) = i + 1}

theorem integrable_chart_of_eq_zero (hD : ChartDecay ds i j hj)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ complexStandardModule n ds)
    (h1 : h 1 = 0) : Integrable fun z => h (chart i j hj z) := by
  obtain ⟨C, hC⟩ := (hD h hh).2 h1
  exact integrable_of_bound (contDiff_apply_chart hh.1 i j hj).continuous hC

theorem contDiff_one_chart {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n ds) :
    ContDiff ℝ 1 fun z => h (chart i j hj z) :=
  (contDiff_apply_chart hh.1 i j hj).of_le (by exact_mod_cast le_top)

theorem integrable_rightDerivative_chart (LF : ChartLieFacts ds hn i j hj)
    (hD : ChartDecay ds i j hj) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ a b : Fin n, b ≤ a → X a b = 0) {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n ds) :
    Integrable fun z => rightDerivative (matrixModel ℂ n) X h (chart i j hj z) :=
  integrable_chart_of_eq_zero hD (rightDerivative_mem_principalSeries _ hh X)
    (LF.one_strictUpper h hh X hX)

/-- `∫ R(X) h (s x(z)) dz = 0` for `X` strictly upper triangular. -/
theorem integral_rightDerivative_chart (LF : ChartLieFacts ds hn i j hj)
    (hD : ChartDecay ds i j hj) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ a b : Fin n, b ≤ a → X a b = 0) {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n ds) :
    ∫ z, rightDerivative (matrixModel ℂ n) X h (chart i j hj z) = 0 := by
  have hpt : ∀ z, rightDerivative (matrixModel ℂ n) X h (chart i j hj z) =
      ((X i j).re : ℂ) * fderiv ℝ (fun z => h (chart i j hj z)) z 1 +
        ((X i j).im : ℂ) * fderiv ℝ (fun z => h (chart i j hj z)) z Complex.I := by
    intro z
    have hadd := rightDerivative_add (X - Matrix.single i j (X i j)) (Matrix.single i j (X i j))
      h (chart i j hj z)
    rw [sub_add_cancel] at hadd
    rw [hadd, LF.strictUpper h hh _ (strictUpper_sub_single hj hX) (by simp), zero_add,
      LF.single_ij h hh, clm_apply_eq]
  have hint : ∀ w : ℂ, Integrable fun z => fderiv ℝ (fun z => h (chart i j hj z)) z w := by
    intro w
    refine (integrable_rightDerivative_chart LF hD (strictUpper_single hj w) hh).congr
      (Eventually.of_forall fun z => ?_)
    exact LF.single_ij h hh w z
  have hlim : Tendsto (fun z => h (chart i j hj z)) (Bornology.cobounded ℂ) (𝓝 0) := by
    obtain ⟨C, hC⟩ := (hD h hh).1
    exact tendsto_cobounded_of_bound hC
  have h1 := integral_fderiv_one_eq_zero (contDiff_one_chart hh) (hint 1) hlim
  have hI := integral_fderiv_I_eq_zero (contDiff_one_chart hh) (hint Complex.I) hlim
  simp only [hpt]
  rw [integral_add ((hint 1).const_mul _) ((hint Complex.I).const_mul _), integral_const_mul,
    integral_const_mul, h1, hI, mul_zero, mul_zero, add_zero]

/-- The bound on `Dφ_g(z)(c z)` for `g(1) = 0`. -/
theorem exists_bound_fderiv_mul (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    {g : Langlands.GeneralLinear n ℂ → ℂ} (hg : g ∈ complexStandardModule n ds) (hg1 : g 1 = 0)
    (c : ℂ) :
    ∃ C, ∀ z, ‖fderiv ℝ (fun z => g (chart i j hj z)) z (c * z)‖ ≤
      C * ((1 + ‖z‖) ^ 3)⁻¹ := by
  set h : Langlands.GeneralLinear n ℂ → ℂ :=
    rightDerivative (matrixModel ℂ n) (Matrix.single j j c) g - kappa ds hn i c • g with hh_def
  have hh : h ∈ complexStandardModule n ds :=
    Submodule.sub_mem _ (rightDerivative_mem_principalSeries _ hg _)
      (Submodule.smul_mem _ _ hg)
  have h1 : h 1 = 0 := by
    simp only [hh_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LF.one_diag g hg j c, hg1,
      mul_zero, sub_zero]
  obtain ⟨C, hC⟩ := (hD h hh).2 h1
  refine ⟨C, fun z => ?_⟩
  have hz : h (chart i j hj z) = fderiv ℝ (fun z => g (chart i j hj z)) z (c * z) := by
    simp only [hh_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LF.diag_j g hg c z]
    ring
  rw [← hz]
  exact hC z

theorem integrable_fderiv_mul (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    {g : Langlands.GeneralLinear n ℂ → ℂ} (hg : g ∈ complexStandardModule n ds) (hg1 : g 1 = 0)
    (c : ℂ) : Integrable fun z => fderiv ℝ (fun z => g (chart i j hj z)) z (c * z) := by
  obtain ⟨C, hC⟩ := exists_bound_fderiv_mul LF hD hg hg1 c
  have hcont : Continuous fun z => fderiv ℝ (fun z => g (chart i j hj z)) z (c * z) :=
    ((contDiff_one_chart hg).continuous_fderiv one_ne_zero).clm_apply
      (continuous_const.mul continuous_id)
  exact integrable_of_bound hcont hC

/-- The two bounds of the integration-by-parts lemmas, with a common constant. -/
theorem exists_common_bound (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    {g : Langlands.GeneralLinear n ℂ → ℂ} (hg : g ∈ complexStandardModule n ds) (hg1 : g 1 = 0)
    (c : ℂ) :
    ∃ C, (∀ z, ‖g (chart i j hj z)‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹) ∧
      ∀ z, ‖fderiv ℝ (fun z => g (chart i j hj z)) z (c * z)‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹ := by
  obtain ⟨C₁, hC₁⟩ := (hD g hg).2 hg1
  obtain ⟨C₂, hC₂⟩ := exists_bound_fderiv_mul LF hD hg hg1 c
  have h₁ : 0 ≤ C₁ := nonneg_of_bound hC₁
  have h₂ : 0 ≤ C₂ := nonneg_of_bound hC₂
  refine ⟨C₁ + C₂, fun z => le_add_bound (hC₁ z) (by positivity) h₂, fun z => ?_⟩
  rw [add_comm]
  exact le_add_bound (hC₂ z) (by positivity) h₁

/-- Euler's identity along the chart: `∫ Dφ_g(z)(1 · z) = -2 ∫ φ_g` when `g(1) = 0`. -/
theorem integral_fderiv_one_mul (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    {g : Langlands.GeneralLinear n ℂ → ℂ} (hg : g ∈ complexStandardModule n ds)
    (hg1 : g 1 = 0) :
    ∫ z, fderiv ℝ (fun z => g (chart i j hj z)) z (1 * z) =
      -2 * ∫ z, g (chart i j hj z) := by
  obtain ⟨C, hC, hC'⟩ := exists_common_bound LF hD hg hg1 1
  simp only [one_mul] at hC' ⊢
  exact integral_fderiv_apply_self (contDiff_one_chart hg) hC hC'

/-- `∫ Dφ_g(z)(i z) = 0` when `g(1) = 0`. -/
theorem integral_fderiv_I_mul (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    {g : Langlands.GeneralLinear n ℂ → ℂ} (hg : g ∈ complexStandardModule n ds)
    (hg1 : g 1 = 0) :
    ∫ z, fderiv ℝ (fun z => g (chart i j hj z)) z (Complex.I * z) = 0 := by
  obtain ⟨C, hC, hC'⟩ := exists_common_bound LF hD hg hg1 Complex.I
  exact integral_fderiv_apply_I_mul_self (contDiff_one_chart hg) hC hC'

end Generic

/-! ## The functional -/

section Functional

variable (ds : List ComplexCharacterData) (hn : ds.length = n) {i : Fin n} (j : Fin n)

/-- `g_c(v) = R(c E_jj) v - κ_j(c) v`. -/
def shift (c : ℂ) : KFs n ds →ₗ[ℂ] KFs n ds :=
  complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single j j c) - kappa ds hn j c • LinearMap.id

variable {ds hn j}

theorem coe_shift (c : ℂ) (v : KFs n ds) :
    ((shift ds hn j c v : KFs n ds) : Langlands.GeneralLinear n ℂ → ℂ) =
      rightDerivative (matrixModel ℂ n) (Matrix.single j j c) v -
        kappa ds hn j c • (v : Langlands.GeneralLinear n ℂ → ℂ) := by
  simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Submodule.coe_sub, Submodule.coe_smul, coe_lie]

variable {hj : (j : ℕ) = i + 1}

theorem integrand_eq_shift (c : ℂ) (v : KFs n ds) (z : ℂ) :
    integrand ds hn i j hj c v z =
      (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ) (chart i j hj z) := by
  rw [coe_shift]
  rfl

theorem shift_apply_one (LF : ChartLieFacts ds hn i j hj) (c : ℂ) (v : KFs n ds) :
    (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ) 1 = 0 := by
  rw [coe_shift, Pi.sub_apply, Pi.smul_apply, LF.one_diag v (mem_of_mem_kFs v.2) j c,
    smul_eq_mul, sub_self]

theorem integrable_shift (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c : ℂ) (v : KFs n ds) :
    Integrable fun z => (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ) (chart i j hj z) :=
  integrable_chart_of_eq_zero hD (mem_of_mem_kFs (shift ds hn j c v).2) (shift_apply_one LF c v)

/-- The rank-one Jacquet functional `Λ_c(v) = ∫ (R(c E_jj) v - κ_j(c) v)(s x(z)) dz`. -/
def functional (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj) (c : ℂ) :
    KFs n ds →ₗ[ℂ] ℂ where
  toFun v := ∫ z, (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ) (chart i j hj z)
  map_add' v w := by
    rw [map_add, Submodule.coe_add]
    exact integral_add (integrable_shift LF hD c v) (integrable_shift LF hD c w)
  map_smul' a v := by
    rw [map_smul, Submodule.coe_smul]
    exact integral_const_mul a _

theorem functional_apply (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c : ℂ) (v : KFs n ds) :
    functional LF hD c v = ∫ z, integrand ds hn i j hj c v z := by
  simp only [integrand_eq_shift]
  rfl

theorem functional_apply_shift (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c : ℂ) (v : KFs n ds) :
    functional LF hD c v =
      ∫ z, (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ) (chart i j hj z) :=
  rfl

/-- `Λ_c` vanishes on `𝔫 V`. -/
theorem functional_strictUpper (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : ∀ a b : Fin n, (b : ℕ) ≤ a → X a b = 0)
    (v : KFs n ds) :
    functional LF hD c (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) v) = 0 := by
  have hX' : ∀ a b : Fin n, b ≤ a → X a b = 0 := fun a b h => hX a b h
  have hY := single_mul_strict_sub_mem j c X hX'
  have hshift : shift ds hn j c (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) v) =
      complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) (shift ds hn j c v) +
        complexStandardLie n ds
          ((1 : ℂ) ⊗ₜ[ℝ] (Matrix.single j j c * X - X * Matrix.single j j c)) v := by
    simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul]
    rw [lie_comm (Matrix.single j j c) X v]
    abel
  rw [functional_apply_shift, hshift, Submodule.coe_add, coe_lie, coe_lie]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_rightDerivative_chart LF hD hX' (mem_of_mem_kFs (shift ds hn j c v).2))
      (integrable_rightDerivative_chart LF hD hY (mem_of_mem_kFs v.2)),
    integral_rightDerivative_chart LF hD hX' (mem_of_mem_kFs (shift ds hn j c v).2),
    integral_rightDerivative_chart LF hD hY (mem_of_mem_kFs v.2), add_zero]

/-- `Λ_c(R(c' E_kk) v) = ∫ R(c' E_kk) g_c(v) (s x(z)) dz`. -/
theorem functional_diag (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c c' : ℂ) (k : Fin n) (v : KFs n ds) :
    functional LF hD c (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single k k c') v) =
      ∫ z, rightDerivative (matrixModel ℂ n) (Matrix.single k k c')
        (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ) (chart i j hj z) := by
  have hshift : shift ds hn j c
      (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single k k c') v) =
      complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single k k c') (shift ds hn j c v) := by
    simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul]
    rw [lie_comm (Matrix.single j j c) (Matrix.single k k c') v, single_commute,
      TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply, add_zero]
  rw [functional_apply_shift, hshift, coe_lie]

theorem functional_diag_other (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c c' : ℂ) (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) (v : KFs n ds) :
    functional LF hD c (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single k k c') v) =
      kappa ds hn k c' * functional LF hD c v := by
  have hg := mem_of_mem_kFs (shift ds hn j c v).2
  rw [functional_diag]
  simp only [LF.diag_other _ hg k hki hkj c']
  rw [integral_const_mul]
  rfl

theorem functional_diag_j (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c c' : ℂ) (v : KFs n ds) :
    functional LF hD c (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single j j c') v) =
      kappa ds hn i c' * functional LF hD c v +
        ∫ z, fderiv ℝ (fun z => (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ)
          (chart i j hj z)) z (c' * z) := by
  have hg := mem_of_mem_kFs (shift ds hn j c v).2
  rw [functional_diag]
  simp only [LF.diag_j _ hg c']
  rw [integral_add ((integrable_shift LF hD c v).const_mul _)
      (integrable_fderiv_mul LF hD hg (shift_apply_one LF c v) c'),
    integral_const_mul]
  rfl

theorem functional_diag_i (LF : ChartLieFacts ds hn i j hj) (hD : ChartDecay ds i j hj)
    (c c' : ℂ) (v : KFs n ds) :
    functional LF hD c (complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single i i c') v) =
      kappa ds hn j c' * functional LF hD c v -
        ∫ z, fderiv ℝ (fun z => (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ)
          (chart i j hj z)) z (c' * z) := by
  have hg := mem_of_mem_kFs (shift ds hn j c v).2
  rw [functional_diag]
  simp only [LF.diag_i _ hg c']
  rw [integral_sub ((integrable_shift LF hD c v).const_mul _)
      (integrable_fderiv_mul LF hD hg (shift_apply_one LF c v) c'),
    integral_const_mul]
  rfl

/-- **`Λ_c` is a Jacquet functional** with the exponents of `ds` at the positions `i` and `j`
swapped: `a_i = κ_j(1) + 2`, `a_j = κ_i(1) - 2`, `b_i = κ_j(i)`, `b_j = κ_i(i)`, and
`a_k = κ_k(1)`, `b_k = κ_k(i)` otherwise. -/
theorem isComplexJacquetFunctional_functional (LF : ChartLieFacts ds hn i j hj)
    (hD : ChartDecay ds i j hj) (c : ℂ) {a b : Fin n → ℂ}
    (ha : ∀ k, k ≠ i → k ≠ j → a k = kappa ds hn k 1) (hai : a i = kappa ds hn j 1 + 2)
    (haj : a j = kappa ds hn i 1 - 2)
    (hb : ∀ k, k ≠ i → k ≠ j → b k = kappa ds hn k Complex.I)
    (hbi : b i = kappa ds hn j Complex.I) (hbj : b j = kappa ds hn i Complex.I) :
    IsComplexJacquetFunctional n (complexStandardLie n ds) (functional LF hD c) a b := by
  have hg : ∀ v : KFs n ds,
      (shift ds hn j c v : Langlands.GeneralLinear n ℂ → ℂ) ∈ complexStandardModule n ds :=
    fun v => mem_of_mem_kFs (shift ds hn j c v).2
  refine ⟨fun X hX v => functional_strictUpper LF hD c X hX v, fun k v => ?_⟩
  by_cases hki : k = i
  · subst hki
    rw [functional_diag_i, functional_diag_i, hai, hbi,
      integral_fderiv_one_mul LF hD (hg v) (shift_apply_one LF c v),
      integral_fderiv_I_mul LF hD (hg v) (shift_apply_one LF c v), ← functional_apply_shift LF hD]
    constructor <;> ring
  · by_cases hkj : k = j
    · subst hkj
      rw [functional_diag_j, functional_diag_j, haj, hbj,
        integral_fderiv_one_mul LF hD (hg v) (shift_apply_one LF c v),
        integral_fderiv_I_mul LF hD (hg v) (shift_apply_one LF c v), ← functional_apply_shift LF hD]
      constructor <;> ring
    · rw [functional_diag_other LF hD c 1 k hki hkj, functional_diag_other LF hD c _ k hki hkj,
        ha k hki hkj, hb k hki hkj]
      exact ⟨rfl, rfl⟩

end Functional

/-! ## Specialization to an adjacent swap -/

section Specialize

theorem kappa_one (ds : List ComplexCharacterData) (hn : ds.length = n) (k : Fin n) :
    kappa ds hn k 1 =
      2 * (ds.get (Fin.cast hn.symm k)).exponent + ((n : ℂ) - 1) - 2 * ((k : ℕ) : ℂ) := by
  simp [kappa]

theorem kappa_I (ds : List ComplexCharacterData) (hn : ds.length = n) (k : Fin n) :
    kappa ds hn k Complex.I = Complex.I * ((ds.get (Fin.cast hn.symm k)).weight : ℂ) := by
  simp [kappa]

theorem getElem_append_cons_cons_left (pre post : List ComplexCharacterData)
    (x y : ComplexCharacterData) (m : ℕ) (hm : m = pre.length)
    (h : m < (pre ++ x :: y :: post).length) : (pre ++ x :: y :: post)[m] = x := by
  subst hm
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

theorem getElem_append_cons_cons_right (pre post : List ComplexCharacterData)
    (x y : ComplexCharacterData) (m : ℕ) (hm : m = pre.length + 1)
    (h : m < (pre ++ x :: y :: post).length) : (pre ++ x :: y :: post)[m] = y := by
  subst hm
  rw [List.getElem_append_right (Nat.le_succ _)]
  simp

theorem getElem_append_cons_cons_of_ne (pre post : List ComplexCharacterData)
    (x y x' y' : ComplexCharacterData) (m : ℕ) (h1 : m ≠ pre.length)
    (h2 : m ≠ pre.length + 1) (h : m < (pre ++ x :: y :: post).length)
    (h' : m < (pre ++ x' :: y' :: post).length) :
    (pre ++ x :: y :: post)[m] = (pre ++ x' :: y' :: post)[m] := by
  rcases Nat.lt_or_gt_of_ne h1 with hlt | hgt
  · rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
  · obtain ⟨r, rfl⟩ : ∃ r, m = pre.length + 2 + r := ⟨m - pre.length - 2, by omega⟩
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    have hr : pre.length + 2 + r - pre.length = r + 2 := by omega
    simp only [hr, List.getElem_cons_succ]

/-- **Specialization.** For `ds = pre ++ d :: e :: post` with `Re(t_d - t_e) ≥ 0`, the positions
`i = |pre|`, `j = i + 1`, and the chart formulas `LF`, a nonvanishing integral of the integrand
yields a nonzero Jacquet functional on the `U(n)`-finite vectors of the standard module of `ds`
whose exponents are those of `pre ++ e :: d :: post`. -/
theorem exists_swapJacquetFunctional (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hn : (pre ++ d :: e :: post).length = n)
    (hes : (pre ++ e :: d :: post).length = n) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 ≤ (d.exponent - e.exponent).re)
    (LF : ChartLieFacts (pre ++ d :: e :: post) hn i j hj)
    (hnz : ∃ (c : ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ), f ∈ KFs n (pre ++ d :: e :: post) ∧
      ∫ z, integrand (pre ++ d :: e :: post) hn i j hj c f z ≠ 0) :
    ∃ ℓ : KFs n (pre ++ d :: e :: post) →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
      IsComplexJacquetFunctional n (complexStandardLie n (pre ++ d :: e :: post)) ℓ
        (fun k => 2 * ((pre ++ e :: d :: post).get (Fin.cast hes.symm k)).exponent +
          ((n : ℂ) - 1) - 2 * ((k : ℕ) : ℂ))
        (fun k => Complex.I * (((pre ++ e :: d :: post).get (Fin.cast hes.symm k)).weight : ℂ)) := by
  obtain ⟨c, f, hf, hne⟩ := hnz
  have hgi : ∀ (l : List ComplexCharacterData) (hl : l.length = n) (k : Fin n),
      l.get (Fin.cast hl.symm k) = l[(k : ℕ)]'(by rw [hl]; exact k.2) := fun _ _ _ => rfl
  have hds_i : (pre ++ d :: e :: post).get (Fin.cast hn.symm i) = d := by
    rw [hgi _ hn]; exact getElem_append_cons_cons_left _ _ _ _ _ hi _
  have hds_j : (pre ++ d :: e :: post).get (Fin.cast hn.symm j) = e := by
    rw [hgi _ hn]; exact getElem_append_cons_cons_right _ _ _ _ _ (by omega) _
  have hes_i : (pre ++ e :: d :: post).get (Fin.cast hes.symm i) = e := by
    rw [hgi _ hes]; exact getElem_append_cons_cons_left _ _ _ _ _ hi _
  have hes_j : (pre ++ e :: d :: post).get (Fin.cast hes.symm j) = d := by
    rw [hgi _ hes]; exact getElem_append_cons_cons_right _ _ _ _ _ (by omega) _
  have hother : ∀ k : Fin n, k ≠ i → k ≠ j →
      (pre ++ e :: d :: post).get (Fin.cast hes.symm k) =
        (pre ++ d :: e :: post).get (Fin.cast hn.symm k) := by
    intro k hki hkj
    rw [hgi _ hes, hgi _ hn]
    apply getElem_append_cons_cons_of_ne
    · intro h; exact hki (Fin.ext (by omega))
    · intro h; exact hkj (Fin.ext (by omega))
  refine ⟨functional LF (chartDecay pre post d e i j hi hj hre) c, ?_, ?_⟩
  · intro h0
    apply hne
    rw [← functional_apply LF (chartDecay pre post d e i j hi hj hre) c ⟨f, hf⟩, h0]
    rfl
  · apply isComplexJacquetFunctional_functional
    · intro k hki hkj
      rw [kappa_one, hother k hki hkj]
    · rw [kappa_one, hes_i, hds_j, hj]
      push_cast
      ring
    · rw [kappa_one, hes_j, hds_i, hj]
      push_cast
      ring
    · intro k hki hkj
      rw [kappa_I, hother k hki hkj]
    · rw [kappa_I, hes_i, hds_j]
    · rw [kappa_I, hes_j, hds_i]

end Specialize

end Langlands.Archimedean.ComplexSwapJacquet
