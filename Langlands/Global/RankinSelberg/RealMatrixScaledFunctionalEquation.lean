import Langlands.Global.RankinSelberg.RealMatrixFunctionalEquation

/-! # The real square matrix functional equation for any nonzero Fourier parameter -/

noncomputable section

open MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanDeterminantTheta RealSquareFourier RealGodement RealPrincipalSeries

local instance realScaledMatrixGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realScaledMatrixGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix I I ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "ιg" => inverseTranspose n ℝ
local notation "D" => realMatrixDetScale (r := r)
local notation "dp" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "absC" => fun b : ℝˣ => ((|(b : ℝ)| : ℝ) : ℂ)

/-- Change of self-dual measure and argument in the actual square Fourier transform. -/
theorem realMatrixTransform_scale (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) (X : Mat) :
    matrixTransform b Φ X = absC b ^ (((n : ℕ) : ℂ) * ((n : ℕ) : ℂ) / 2) *
      matrixTransform 1 Φ ((b : ℝ) • X) := by
  simp only [matrixTransform_eq_realRectangularSchwartzFourier]
  let e := rectangularCoordinates (r := (n : ℕ)) (s := (n : ℕ))
  let Ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ
  change scaledEuclideanFourier b Ψ (e.symm X) = _ *
    scaledEuclideanFourier 1 Ψ (e.symm ((b : ℝ) • X))
  have hscale : (euclideanHaarFactor b (EuclideanSpace ℝ (I × I)) : ℂ) =
      absC b ^ (((n : ℕ) : ℂ) * ((n : ℕ) : ℂ) / 2) := by
    simp only [euclideanHaarFactor, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
      Complex.ofReal_cpow (abs_nonneg _)]
    congr 1
    push_cast
    ring
  have hone : euclideanHaarFactor (1 : ℝˣ) (EuclideanSpace ℝ (I × I)) = 1 := by
    simp [euclideanHaarFactor]
  rw [scaledEuclideanFourier_apply, scaledEuclideanFourier_apply, hscale, hone, Complex.ofReal_one, one_mul,
    Units.val_one, one_smul, map_smul e.symm (b : ℝ) X]

/-- The scalar matrix of a real unit. -/
def realMatrixScalar (b : ℝˣ) : G := diagonalMatrixUnits ℝ (fun _ : I => b)

theorem realMatrixScalar_mul_val (b : ℝˣ) (g : G) : (realMatrixScalar b * g).val = (b : ℝ) • g.val := by
  ext i j
  simp only [realMatrixScalar, Units.val_mul, diagonalMatrixUnits_val, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul]

theorem realMatrixScalar_central (b : ℝˣ) (g : G) : g * realMatrixScalar b = realMatrixScalar b * g := by
  apply Units.ext
  ext i j
  simp only [realMatrixScalar, Units.val_mul, diagonalMatrixUnits_val, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact mul_comm _ _

private theorem realMatrixDetScale_scalar (b : ℝˣ) : D (realMatrixScalar b) = |(b : ℝ)| ^ n := by
  simp only [realMatrixScalar, realMatrixDetScale, realNormalizedAbs, diagonalMatrixUnits_val,
    Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, abs_pow]

private theorem inverseTranspose_scalar_inv (b : ℝˣ) : ιg (realMatrixScalar b)⁻¹ = realMatrixScalar b := by
  apply Units.ext
  rw [inverseTranspose_coe, inv_inv, realMatrixScalar, diagonalMatrixUnits_val, Matrix.diagonal_transpose]

private theorem detPower_scalar (b : ℝˣ) (s : ℂ) :
    dp (realMatrixScalar (r := r) b) s = absC b ^ (((n : ℕ) : ℂ) * s) := by
  rw [realDetPower_eq_cpow]
  change (D (realMatrixScalar b) : ℂ) ^ s = _
  rw [realMatrixDetScale_scalar, ← Real.rpow_natCast,
    ← Complex.cpow_mul_ofReal_nonneg (abs_nonneg (b : ℝ)), Complex.ofReal_natCast]

private theorem sum_halfModulus_exponents :
    (∑ i : I, ((((n : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ))) = 0 := by
  let z (i : I) : ℂ := (((n : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ)
  have hRev (i : I) : z i.rev = -z i := by
    have hi : (i.rev : ℕ) = r - i.val := by
      change r + 1 - (i.val + 1) = r - i.val
      omega
    dsimp only [z]
    rw [hi, Nat.cast_sub (Nat.le_of_lt_succ i.isLt)]
    push_cast
    ring
  have he : (∑ i : I, z i.rev) = ∑ i : I, z i :=
    Equiv.sum_comp (Fin.revPerm : Equiv.Perm I) z
  simp only [hRev, Finset.sum_neg_distrib] at he
  change (∑ i : I, z i) = 0
  linear_combination -he / 2

private theorem principalSeriesCharacter_const (χ : ℕ → ℝˣ → ℂ) (b : ℝˣ) :
    principalSeriesCharacter ℝ n χ (fun _ => b) = ∏ i : I, χ i b := by
  have hb : absC b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr b.ne_zero)
  simp only [principalSeriesCharacter, Module.finrank_self, pow_one, Real.norm_eq_abs, Finset.prod_mul_distrib]
  rw [show (∏ i : I, absC b ^ ((((n : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ))) = 1 from ?_, mul_one]
  simp_rw [Complex.cpow_def_of_ne_zero hb]
  rw [← Complex.exp_sum, ← Finset.mul_sum, sum_halfModulus_exponents, mul_zero, Complex.exp_zero]

/-- The scalar action on the coefficient of any linear form of the position principal series. -/
theorem realMatrixFunctionalCoefficient_scalar (ds : List RealBlock)
    (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ) (b : ℝˣ) (g : G) :
    ℓ (translate r ds (realMatrixScalar b * g) f) = (∏ i : I, realPositionCharacter ds i b) *
      ℓ (translate r ds g f) := by
  have h : translate r ds (realMatrixScalar b * g) f =
      (∏ i : I, realPositionCharacter ds i b) • translate r ds g f := by
    apply Subtype.ext
    funext x
    change (f : G → ℂ) (x * (realMatrixScalar b * g)) =
      (∏ i : I, realPositionCharacter ds i b) * (f : G → ℂ) (x * g)
    rw [← mul_assoc, realMatrixScalar_central b x, mul_assoc]
    have hf := f.2.2 (fun _ => b) (1 : upperUnipotent n ℝ) (x * g)
    change (f : G → ℂ) (realMatrixScalar b * (1 : upperUnipotent n ℝ).val * (x * g)) = _ at hf
    simpa only [Subgroup.coe_one, mul_one, principalSeriesCharacter_const] using hf
  rw [h, map_smul, smul_eq_mul]

/-- The scalar equivariance of the inverse-transpose coefficient, as required by the
rescaling of the Fourier parameter. -/
theorem realMatrixFunctionalCoefficient_dual_scalar (ds : List RealBlock)
    (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ) (b : ℝˣ) (g : G) :
    ℓ (translate r ds (ιg ((realMatrixScalar b)⁻¹ * g)) f) =
      (∏ i : I, realPositionCharacter ds i b) * ℓ (translate r ds (ιg g) f) := by
  rw [map_mul, inverseTranspose_scalar_inv]
  exact realMatrixFunctionalCoefficient_scalar ds f ℓ b (ιg g)

/-- The factor relating the dual zeta integral at `b` to that at `1` at the same `s`. -/
def realMatrixScaledDualFactor (b : ℝˣ) (ω : ℂ) (s : ℂ) : ℂ :=
  ω * absC b ^ (((n : ℕ) : ℂ) * (1 / 2 - s))

theorem differentiable_realMatrixScaledDualFactor (b : ℝˣ) (ω : ℂ) :
    Differentiable ℂ (realMatrixScaledDualFactor (r := r) b ω) := by
  have hb : absC b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr b.ne_zero)
  exact (((differentiable_id.const_sub (1 / 2 : ℂ)).const_mul ((n : ℕ) : ℂ)).const_cpow (Or.inl hb)).const_mul _

theorem realMatrixZetaKernel_scaled_dual (b : ℝˣ) (fd : G → ℂ) (ω : ℂ)
    (hω : ∀ g : G, fd ((realMatrixScalar b)⁻¹ * g) = ω * fd g)
    (Φ : 𝓢(Mat, ℂ)) (s : ℂ) (g : G) :
    realMatrixZetaKernel fd (matrixTransform b Φ) s ((realMatrixScalar b)⁻¹ * g) =
      realMatrixScaledDualFactor (r := r) b ω s * realMatrixZetaKernel fd (matrixTransform 1 Φ) s g := by
  have hb : absC b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr b.ne_zero)
  have harg : (b : ℝ) • ((realMatrixScalar b)⁻¹ * g).val = g.val := by
    rw [← realMatrixScalar_mul_val b, mul_inv_cancel_left]
  have hp : absC b ^ (((n : ℕ) : ℂ) * ((n : ℕ) : ℂ) / 2) *
      (absC b ^ (((n : ℕ) : ℂ) * (s + (r : ℂ) / 2)))⁻¹ =
      absC b ^ (((n : ℕ) : ℂ) * (1 / 2 - s)) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hb]
    congr 1
    push_cast
    ring
  simp only [realMatrixZetaKernel, realMatrixScaledDualFactor, realMatrixTransform_scale b, harg,
    hω, realDetPower_mul, realDetPower_inv, detPower_scalar]
  calc
    _ = (absC b ^ (((n : ℕ) : ℂ) * ((n : ℕ) : ℂ) / 2) *
        (absC b ^ (((n : ℕ) : ℂ) * (s + (r : ℂ) / 2)))⁻¹) *
      (ω * (matrixTransform 1 Φ g.val * fd g * dp g (s + (r : ℂ) / 2))) := by ring
    _ = _ := by rw [hp]; ring

/-- The dual zeta integral at the Fourier parameter `b` is the scaled dual factor times the dual
zeta integral at parameter one, at every `s`. -/
theorem realMatrixZeta_scaled_dual (μ : Measure G) [μ.IsHaarMeasure] (b : ℝˣ) (fd : G → ℂ) (ω : ℂ)
    (hω : ∀ g : G, fd ((realMatrixScalar b)⁻¹ * g) = ω * fd g) (Φ : 𝓢(Mat, ℂ)) (s : ℂ) :
    realMatrixZeta μ fd (matrixTransform b Φ) s =
      realMatrixScaledDualFactor (r := r) b ω s * realMatrixZeta μ fd (matrixTransform 1 Φ) s := by
  unfold realMatrixZeta
  rw [← integral_mul_left_eq_self (μ := μ) (realMatrixZetaKernel fd (matrixTransform b Φ) s)
    (realMatrixScalar b)⁻¹, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all μ fun g => realMatrixZetaKernel_scaled_dual b fd ω hω Φ s g)

/-- Rescale the Fourier character in any established real matrix equation whose dual coefficient
has the specified scalar equivariance. -/
theorem realMatrixEquation_scale (μ : Measure G) [μ.IsHaarMeasure]
    (b : ℝˣ) (f fd : G → ℂ) (ω : ℂ)
    (hω : ∀ g : G, fd ((realMatrixScalar b)⁻¹ * g) = ω * fd g)
    (Φ : 𝓢(Mat, ℂ)) (L Ld E : ℂ → ℂ)
    (h : HasRealMatrixEquation μ f Φ fd (matrixTransform 1 Φ) L Ld E) :
    HasRealMatrixEquation μ f Φ fd (matrixTransform b Φ) L Ld
      (fun s => realMatrixScaledDualFactor (r := r) b ω (1 - s) * E s) := by
  let c := realMatrixScaledDualFactor (r := r) b ω
  have hc : Differentiable ℂ c := differentiable_realMatrixScaledDualFactor b ω
  have hZ : realMatrixZeta μ fd (matrixTransform b Φ) =
      fun s => c s * realMatrixZeta μ fd (matrixTransform 1 Φ) s :=
    funext (realMatrixZeta_scaled_dual μ b fd ω hω Φ)
  obtain ⟨σ, M, Md, hInt, hHol, hHold, hM, hMd, hEq, hEqd, hFE⟩ := h
  refine ⟨σ, M, fun s => c s * Md s, ?_, hHol, ?_, hM,
    fun s hs => (hc.analyticAt s).meromorphicAt.mul (hMd s hs), hEq, ?_, ?_⟩
  · intro s hs
    refine ⟨(hInt s hs).1, ?_⟩
    refine (((hInt s hs).2.const_mul (c s)).comp_mul_left (realMatrixScalar b)).congr
      (ae_of_all μ fun g => ?_)
    have hg := realMatrixZetaKernel_scaled_dual b fd ω hω Φ s (realMatrixScalar b * g)
    rw [inv_mul_cancel_left] at hg
    exact hg.symm
  · rw [hZ]
    exact hc.differentiableOn.mul hHold
  · intro s hs
    rw [hZ]
    exact congrArg (fun z : ℂ => c s * z) (hEqd s hs)
  · filter_upwards [hFE] with s hs
    change L s * (c (1 - s) * Md (1 - s)) = (c (1 - s) * E s) * Ld (1 - s) * M s
    linear_combination c (1 - s) * hs

/-- Real matrix continuation and reflection at any nonzero Fourier parameter for compact-
derivative-bounded principal-series coefficients, with the exact scalar and size correction. -/
def RealMatrixCompactFunctionalEquationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ),
    HasCompactDerivativeBound r ds ℓ → ∀ (Φ : 𝓢(Mat, ℂ)) (b : ℝˣ),
    let e (i : I) := RealBlockPosition.realPositionSign ds i
    let u (i : I) := GramFormula.realPositionExponent ds i
    let F (g : G) := ℓ (translate r ds g f)
    let E (s : ℂ) := torusEpsilon e * (∏ i : I, realPositionCharacter ds i b) *
      absC b ^ (((n : ℕ) : ℂ) * (s - 1 / 2))
    HasRealMatrixEquation μ F Φ (F ∘ ιg) (matrixTransform b Φ) (torusL e u) (torusL e (-u)) E

theorem realMatrixCompactFunctionalEquation : RealMatrixCompactFunctionalEquationStatement (r := r) := by
  intro μ hμ κ hκ hκs ds f ℓ hℓ Φ b e u F E
  let ω := ∏ i : I, realPositionCharacter ds i b
  have hω (g : G) : (F ∘ ιg) ((realMatrixScalar b)⁻¹ * g) = ω * (F ∘ ιg) g :=
    realMatrixFunctionalCoefficient_dual_scalar ds f ℓ b g
  have h1 := realMatrixCompactFunctionalEquationAtOne (r := r) μ κ ds f ℓ hℓ Φ
  have h := realMatrixEquation_scale μ b F (F ∘ ιg) ω hω Φ (torusL e u) (torusL e (-u))
    (fun _ => torusEpsilon e) h1
  have hE (s : ℂ) : realMatrixScaledDualFactor (r := r) b ω (1 - s) * torusEpsilon e = E s := by
    simp only [E, realMatrixScaledDualFactor, ω]
    rw [show (1 : ℂ) / 2 - (1 - s) = s - 1 / 2 by ring]
    ring
  simp_rw [hE] at h
  exact h

end Langlands.GodementJacquet
