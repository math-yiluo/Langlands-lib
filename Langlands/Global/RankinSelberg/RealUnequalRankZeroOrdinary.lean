import Langlands.Global.RankinSelberg.InfiniteWhittakerActualRanges
import Langlands.Global.RankinSelberg.UnequalPlaceTestsFromOrdinary
import Langlands.Global.RankinSelberg.RealRankZeroLocal
import Langlands.Global.RankinSelberg.RealUniformLocalTheoryReduction
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Global.RankinSelberg.ArchimedeanActualWhittakerIntertwiners
import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization
import Mathlib.Analysis.MellinInversion

/-! # Ordinary nonvanishing at a real place when the smaller group is `GL₁`

The case `t = 0` of `RealUnequalOrdinaryPlaceTestsStatement`: the normalized actual coefficient
and its right derivative along `E₀₁` cannot both have ordinary integrals vanishing on right
half-planes, by Mellin inversion of the even and odd parts of `x ↦ W(diag(x, 1)) W'(x)`. The
cases `0 < t` are stated separately and imply the full statement. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology NNReal Real Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

local instance rankZeroOrdinaryAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance rankZeroOrdinarySmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

namespace RealUnequalRankZero

open Langlands.LocalFactor.Archimedean

/-! ### Mellin inversion on the two half-lines -/

/-- A Lebesgue integral on `ℝ` is the integral over `(0, ∞)` of the sum of the values at
`t` and `-t`. -/
theorem integral_eq_integral_Ioi_add_neg {φ : ℝ → ℂ} (hφ : Integrable φ) :
    ∫ x, φ x = ∫ t in Ioi 0, (φ t + φ (-t)) := by
  rw [integral_add hφ.integrableOn hφ.comp_neg.integrableOn, integral_comp_neg_Ioi, neg_zero,
    ← compl_Ioi, integral_add_compl measurableSet_Ioi hφ]

/-- A function whose Mellin transform vanishes on a vertical line of convergence and which is
continuous at `1` vanishes at `1`. -/
theorem eq_zero_of_mellin_eq_zero {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ)
    (hz : ∀ y : ℝ, mellin f (σ + y * I) = 0) (hc : ContinuousAt f 1) : f 1 = 0 := by
  have hV : VerticalIntegrable (mellin f) σ := by
    simp only [VerticalIntegrable, hz]
    exact integrable_zero _ _ _
  rw [← mellinInv_mellin_eq σ f one_pos hf hV hc]
  simp [mellinInv, hz]


/-! ### The first simple root and its modulation -/

open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit transvection_apply)

local notation "G" => fun n => Langlands.GeneralLinear (n + 1) ℝ

/-- The elementary upper unipotent matrix `1 + z E₀₁` of `GL_(r+1)(ℝ)`. -/
def firstRoot {r : ℕ} (h : 0 < r) (z : ℝ) : GeneralLinear.upperUnipotent (r + 1) ℝ :=
  adjacentUnit ⟨0, h⟩ z

/-- The matrix unit `E₀₁` of `𝔤𝔩_(r+1)(ℝ)`. -/
def firstRootDirection {r : ℕ} (h : 0 < r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.single (Fin.castSucc (⟨0, h⟩ : Fin r)) (Fin.succ (⟨0, h⟩ : Fin r)) 1

theorem character_firstRoot {r : ℕ} (h : 0 < r) (a : ℝˣ) (z : ℝ) :
    realWhittakerCharacter a (firstRoot h z).val =
      (Real.fourierChar ((a : ℝ) * z) : ℂ) := by
  let i : Fin r := ⟨0, h⟩
  unfold realWhittakerCharacter
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply]
  congr 3
  change (∑ j : Fin r, Matrix.transvection i.castSucc i.succ z j.castSucc j.succ) = z
  simp only [transvection_apply, ne_of_lt Fin.castSucc_lt_succ, ite_false, zero_add,
    Fin.castSucc_inj, Fin.succ_inj, and_self]
  simp

theorem firstRoot_val_coe {r : ℕ} (h : 0 < r) (z : ℝ) :
    (((firstRoot h z).val : Langlands.GeneralLinear (r + 1) ℝ) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) = 1 + z • firstRootDirection h := by
  change Matrix.transvection _ _ z = _
  rw [Matrix.transvection, firstRootDirection, Matrix.smul_single, smul_eq_mul, mul_one]

theorem pad_mul_firstRoot {r : ℕ} (h : 0 < r) (g : G 0) (z : ℝ) :
    padGL (Nat.succ_le_succ h.le) g * (firstRoot h z).val =
      (firstRoot h (g.val.det * z)).val * padGL (Nat.succ_le_succ h.le) g := by
  let i : Fin r := ⟨0, h⟩
  let A := padGL (Nat.succ_le_succ h.le) g
  have hcol (k : Fin (r + 1)) : A.val k i.castSucc = if k = i.castSucc then g.val.det else 0 := by
    rw [UnequalAnalytic.padGL_apply]
    by_cases hk : k = i.castSucc
    · subst k
      have hi : i.castSucc.val < 1 := Nat.zero_lt_one
      rw [dite_eq_left ⟨hi, hi⟩, ite_eq_left rfl, Matrix.det_fin_one]
      rfl
    · have hk0 : ¬ k.val < 1 := by
        intro hk1
        apply hk
        exact Fin.ext (by change k.val = 0; omega)
      rw [dite_eq_right (fun h' => hk0 h'.1), Matrix.one_apply_ne hk, ite_eq_right hk]
  have hrow (k : Fin (r + 1)) : A.val i.succ k = if i.succ = k then 1 else 0 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (fun h' => by
      have h'1 := h'.1
      change 1 < 1 at h'1
      omega), Matrix.one_apply]
  apply Units.ext
  change A.val * (1 + Matrix.single i.castSucc i.succ z) =
    (1 + Matrix.single i.castSucc i.succ (g.val.det * z)) * A.val
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext k l
  by_cases hk : k = i.castSucc
  · subst k
    rw [Matrix.single_mul_apply_same, hrow]
    by_cases hl : l = i.succ
    · subst l
      rw [Matrix.mul_single_apply_same, hcol, ite_eq_left rfl, ite_eq_left rfl, mul_one]
    · rw [Matrix.mul_single_apply_of_ne z _ _ _ _ hl, ite_eq_right (Ne.symm hl), mul_zero]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hk]
    by_cases hl : l = i.succ
    · subst l
      rw [Matrix.mul_single_apply_same, hcol, ite_eq_right hk, zero_mul]
    · rw [Matrix.mul_single_apply_of_ne z _ _ _ _ hl]


open Langlands.Archimedean (rightDerivative matrixModel unitsExtension unitsExtension_val
  rightDerivative_eq_fderiv_mul_left differentiableAt_unitsExtension_mul_left)

theorem hasDerivAt_fourierChar_mul (c : ℝ) :
    HasDerivAt (fun t : ℝ => (Real.fourierChar (c * t) : ℂ)) (2 * π * c * I) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((2 * π * c : ℝ) : ℂ) * I * (t : ℂ))
      (((2 * π * c : ℝ) : ℂ) * I) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (((2 * π * c : ℝ) : ℂ) * I)
  have h2 := h1.cexp
  have hfun : (fun t : ℝ => (Real.fourierChar (c * t) : ℂ)) =
      fun t : ℝ => Complex.exp (((2 * π * c : ℝ) : ℂ) * I * (t : ℂ)) := by
    funext t
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [hfun]
  convert h2 using 1
  simp

/-- Along `E₀₁`, the right derivative of a smooth function with the left character of `a`, at
`diag(g, 1, …, 1)` with `g ∈ GL₁(ℝ)`, is multiplication by `2πi a det g`. -/
theorem rightDerivative_firstRoot_pad {r : ℕ} (h : 0 < r) {a : ℝˣ} {W : G r → ℂ}
    (hW : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (hleft : ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) = realWhittakerCharacter a u * W g)
    (g : G 0) :
    rightDerivative (matrixModel ℝ (r + 1)) (firstRootDirection h) W
        (padGL (Nat.succ_le_succ h.le) g) =
      (2 * π * (a : ℝ) * g.val.det * I : ℂ) * W (padGL (Nat.succ_le_succ h.le) g) := by
  set P := padGL (Nat.succ_le_succ h.le) g
  rw [rightDerivative_eq_fderiv_mul_left hW]
  set L := fun y : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ =>
    unitsExtension W ((P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) * y)
  have hL : DifferentiableAt ℝ L 1 := differentiableAt_unitsExtension_mul_left hW P
  have hcurve : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) +
      t • firstRootDirection h) (firstRootDirection h) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (firstRootDirection h)).const_add
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
  have hcomp := hL.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
  have hfun : (L ∘ fun t : ℝ => (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) +
      t • firstRootDirection h) =
      fun t => (Real.fourierChar ((a : ℝ) * g.val.det * t) : ℂ) * W P := by
    funext t
    simp only [Function.comp_apply, L]
    rw [← firstRoot_val_coe h t, ← Units.val_mul, unitsExtension_val, pad_mul_firstRoot,
      hleft _ (firstRoot h _).2, character_firstRoot, mul_assoc]
  rw [hfun] at hcomp
  have hder := (hasDerivAt_fourierChar_mul ((a : ℝ) * g.val.det)).mul_const (W P)
  have := hcomp.unique hder
  rw [this]
  push_cast
  ring


/-! ### The rank-zero ordinary integrand on the line -/

open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open RealRankZero (quotientUnits unitsExtend unitsExtend_val quotientUnits_symm_out
  detPower_tateScalarEquiv det_val_tateScalarEquiv)

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanRealNMeasurable
  archimedeanRealNBorel RealRankZero.unitsMeasurable RealRankZero.unitsBorel

local notation "sc" => Langlands.GodementJacquet.tateScalarEquiv ℝ

/-- The part `W(diag(g, 1)) W'(g)` of the ordinary integrand with smaller group `GL₁`, which
does not depend on the spectral variable. -/
def pairProduct {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ)
    (q : LeftUnipotentQuotient 0 ℝ) : ℂ :=
  W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) q.out) * W' q.out

/-- `pairProduct` extended to `ℝ` by zero at the origin. -/
def lineProduct {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) (x : ℝ) : ℂ :=
  unitsExtend (pairProduct h W W') x

theorem lineProduct_units {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) (u : ℝˣ) :
    lineProduct h W W' u = W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (sc u)) * W' (sc u) := by
  rw [lineProduct, unitsExtend_val, pairProduct, quotientUnits_symm_out]

theorem lineProduct_zero {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) :
    lineProduct h W W' 0 = 0 := by
  simp [lineProduct, unitsExtend]

theorem lineProduct_one {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) :
    lineProduct h W W' 1 = W 1 * W' 1 := by
  have h1 := lineProduct_units h W W' 1
  rw [map_one, map_one] at h1
  simpa using h1

theorem unitsExtend_integrand {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) (s : ℂ)
    (x : ℝ) :
    unitsExtend (realUnequalIntegrand h W W' s) x =
      lineProduct h W W' x * ((|x| : ℝ) : ℂ) ^ (s - (r : ℂ) / 2) := by
  by_cases hx : x = 0
  · simp [hx, unitsExtend, lineProduct]
  · have hu : x = (Units.mk0 x hx : ℝ) := rfl
    rw [hu, unitsExtend_val, lineProduct_units]
    simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand]
    rw [quotientUnits_symm_out, detPower_tateScalarEquiv, Nat.sub_zero]

/-- Along `E₀₁` the product on the line acquires the factor `2πi a x`. -/
theorem lineProduct_rightDerivative {r : ℕ} (h : 0 < r) {a : ℝˣ} {W : G r → ℂ}
    (hW : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (hleft : ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) = realWhittakerCharacter a u * W g) (W' : G 0 → ℂ) (x : ℝ) :
    lineProduct h (rightDerivative (matrixModel ℝ (r + 1)) (firstRootDirection h) W) W' x =
      (2 * π * (a : ℝ) * x * I : ℂ) * lineProduct h W W' x := by
  by_cases hx : x = 0
  · simp [hx, lineProduct_zero]
  · have hu : x = (Units.mk0 x hx : ℝ) := rfl
    rw [hu, lineProduct_units, lineProduct_units,
      rightDerivative_firstRoot_pad h hW hleft (sc (Units.mk0 x hx)), det_val_tateScalarEquiv]
    ring

theorem continuousAt_lineProduct {r : ℕ} (h : 0 < r) {W : G r → ℂ} {W' : G 0 → ℂ}
    (hW : Continuous W) (hW' : Continuous W') (u : ℝˣ) :
    ContinuousAt (lineProduct h W W') u := by
  rw [← Units.isOpenEmbedding_val.continuousAt_iff]
  have hfun : (lineProduct h W W' ∘ Units.val) = fun u : ℝˣ =>
      W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (sc u)) * W' (sc u) :=
    funext fun u => lineProduct_units h W W' u
  rw [hfun]
  exact ((hW.comp ((UnequalAnalytic.continuous_padGL _).comp (map_continuous sc))).mul
    (hW'.comp (map_continuous sc))).continuousAt


/-! ### Mellin transforms of the even and odd parts -/

/-- The extension by zero of the rank-zero ordinary integrand, multiplied by `|x|⁻¹`. For a
compatible quotient measure `D.measure = κ • (unitsHaar.map quotientUnits.symm)`, the ordinary
integral is `κ` times the Lebesgue integral of this function (`integral_eq_weighted`). -/
def weighted {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  ((|x|⁻¹ : ℝ) : ℂ) * unitsExtend (realUnequalIntegrand h W W' s) x

theorem cpow_sub_one_of_pos {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (t : ℂ) ^ (z - 1) = ((t⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ z := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one,
    Complex.ofReal_inv]
  ring

theorem weighted_add_neg {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) (s : ℂ) {t : ℝ}
    (ht : 0 < t) :
    weighted h W W' s t + weighted h W W' s (-t) =
      (t : ℂ) ^ (s - (r : ℂ) / 2 - 1) • (lineProduct h W W' t + lineProduct h W W' (-t)) := by
  rw [weighted, weighted, unitsExtend_integrand, unitsExtend_integrand, abs_neg,
    abs_of_pos ht, cpow_sub_one_of_pos ht, smul_eq_mul]
  ring

theorem weighted_add_neg_rightDerivative {r : ℕ} (h : 0 < r) {a : ℝˣ} {W : G r → ℂ}
    (hW : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (hleft : ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) = realWhittakerCharacter a u * W g) (W' : G 0 → ℂ) (s : ℂ) {t : ℝ}
    (ht : 0 < t) :
    weighted h (rightDerivative (matrixModel ℝ (r + 1)) (firstRootDirection h) W) W' s t +
        weighted h (rightDerivative (matrixModel ℝ (r + 1)) (firstRootDirection h) W) W' s (-t) =
      (2 * π * (a : ℝ) * I : ℂ) * ((t : ℂ) ^ (s - (r : ℂ) / 2 + 1 - 1) •
        (lineProduct h W W' t - lineProduct h W W' (-t))) := by
  rw [weighted, weighted, unitsExtend_integrand, unitsExtend_integrand, abs_neg,
    abs_of_pos ht, lineProduct_rightDerivative h hW hleft, lineProduct_rightDerivative h hW hleft,
    add_sub_cancel_right, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_inv]
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp
  ring

variable {D : RealQuotientMeasureData 0} {κ : ℝ≥0}

theorem integrable_weighted (hκ0 : κ ≠ 0)
    (hκ : D.measure = κ • RealRankZero.unitsHaar.map quotientUnits.symm) {r : ℕ} (h : 0 < r)
    {W : G r → ℂ} {W' : G 0 → ℂ} {s : ℂ}
    (hint : Integrable (realUnequalIntegrand h W W' s) D.measure) :
    Integrable (weighted h W W' s) :=
  (RealRankZero.integrable_iff hκ0 hκ _).mp hint

theorem integral_eq_weighted (hκ : D.measure = κ • RealRankZero.unitsHaar.map quotientUnits.symm)
    {r : ℕ} (h : 0 < r) (W : G r → ℂ) (W' : G 0 → ℂ) (s : ℂ) :
    realUnequalIntegral h D W W' s = (κ : ℂ) * ∫ x, weighted h W W' s x := by
  change ∫ q, realUnequalIntegrand h W W' s q ∂D.measure = _
  rw [RealRankZero.integral_eq hκ]
  rfl


/-- If the ordinary integrals of `(W, W')` and of `(R(E₀₁) W, W')` vanish on right
half-planes, then `W(1) W'(1) = 0`: their Mellin transforms are those of the even and odd parts
of `x ↦ W(diag(x, 1)) W'(x)`. -/
theorem value_eq_zero_of_integrals_eq_zero {r : ℕ} (h : 0 < r) (D : RealQuotientMeasureData 0)
    {a : ℝˣ} {W : G r → ℂ} {W' : G 0 → ℂ}
    (hW : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (hleft : ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) = realWhittakerCharacter a u * W g) (hW' : Continuous W') {σ₀ : ℝ}
    (hint : ∀ s : ℂ, σ₀ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure)
    (hintX : ∀ s : ℂ, σ₀ < s.re → Integrable (realUnequalIntegrand h
      (rightDerivative (matrixModel ℝ (r + 1)) (firstRootDirection h) W) W' s) D.measure)
    {σ₁ σ₂ : ℝ} (hz : ∀ s : ℂ, σ₁ < s.re → realUnequalIntegral h D W W' s = 0)
    (hzX : ∀ s : ℂ, σ₂ < s.re → realUnequalIntegral h D
      (rightDerivative (matrixModel ℝ (r + 1)) (firstRootDirection h) W) W' s = 0) :
    W 1 * W' 1 = 0 := by
  obtain ⟨κ, hκ0, hκ⟩ := RealRankZero.exists_measure_eq D
  set L := lineProduct h W W' with hLdef
  set WX := rightDerivative (matrixModel ℝ (r + 1)) (firstRootDirection h) W with hWX
  let E : ℝ → ℂ := fun t => L t + L (-t)
  let O : ℝ → ℂ := fun t => L t - L (-t)
  set σ : ℝ := max σ₀ (max σ₁ σ₂) + 2 with hσ
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
  have hc : (2 * π * (a : ℝ) * I : ℂ) ≠ 0 := by
    have ha : (a : ℝ) ≠ 0 := a.ne_zero
    simp [Real.pi_ne_zero, ha, I_ne_zero]
  have hr : (0 : ℝ) ≤ r / 2 := by positivity
  have h₀ : σ₀ ≤ max σ₀ (max σ₁ σ₂) := le_max_left _ _
  have h₁ : σ₁ ≤ max σ₀ (max σ₁ σ₂) := (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : σ₂ ≤ max σ₀ (max σ₁ σ₂) := (le_max_right _ _).trans (le_max_right _ _)
  have hE (y : ℝ) : MellinConvergent E (σ + y * I) ∧ mellin E (σ + y * I) = 0 := by
    set s : ℂ := σ + y * I + (r : ℂ) / 2 with hs
    have hs_re : s.re = σ + r / 2 := by simp [s]
    have hsσ₀ : σ₀ < s.re := by rw [hs_re]; linarith
    have hsσ₁ : σ₁ < s.re := by rw [hs_re]; linarith
    have hφ := integrable_weighted hκ0 hκ h (hint s hsσ₀)
    have hcongr : EqOn (fun t => weighted h W W' s t + weighted h W W' s (-t))
        (fun t => (t : ℂ) ^ ((σ + y * I) - 1) • E t) (Ioi 0) := fun t ht => by
      simp only
      rw [weighted_add_neg h W W' s ht]
      congr 2
      simp only [s]
      ring
    refine ⟨(hφ.integrableOn.add hφ.comp_neg.integrableOn).congr_fun hcongr measurableSet_Ioi,
      ?_⟩
    have h0 := hz s hsσ₁
    rw [integral_eq_weighted hκ, integral_eq_integral_Ioi_add_neg hφ,
      setIntegral_congr_fun measurableSet_Ioi hcongr] at h0
    exact (mul_eq_zero.mp h0).resolve_left hκc
  have hO (y : ℝ) : MellinConvergent O (σ + y * I) ∧ mellin O (σ + y * I) = 0 := by
    set s : ℂ := σ + y * I + (r : ℂ) / 2 - 1 with hs
    have hs_re : s.re = σ + r / 2 - 1 := by simp [s]
    have hsσ₀ : σ₀ < s.re := by rw [hs_re]; linarith
    have hsσ₂ : σ₂ < s.re := by rw [hs_re]; linarith
    have hφ := integrable_weighted hκ0 hκ h (hintX s hsσ₀)
    have hcongr : EqOn (fun t => weighted h WX W' s t + weighted h WX W' s (-t))
        (fun t : ℝ => (2 * π * (a : ℝ) * I : ℂ) * ((t : ℂ) ^ ((σ + y * I) - 1) • O t)) (Ioi 0) :=
      fun t ht => by
        simp only
        rw [weighted_add_neg_rightDerivative h hW hleft W' s ht]
        congr 3
        simp only [s]
        ring
    have hint' : IntegrableOn
        (fun t : ℝ => (2 * π * (a : ℝ) * I : ℂ) * ((t : ℂ) ^ ((σ + y * I) - 1) • O t)) (Ioi 0) :=
      (hφ.integrableOn.add hφ.comp_neg.integrableOn).congr_fun hcongr measurableSet_Ioi
    have hmc : MellinConvergent O (σ + y * I) := by
      have : IntegrableOn (fun t : ℝ => (2 * π * (a : ℝ) * I : ℂ)⁻¹ *
          ((2 * π * (a : ℝ) * I : ℂ) * ((t : ℂ) ^ ((σ + y * I) - 1) • O t))) (Ioi 0) :=
        hint'.const_mul (2 * π * (a : ℝ) * I : ℂ)⁻¹
      refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
      simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    refine ⟨hmc, ?_⟩
    have h0 := hzX s hsσ₂
    rw [integral_eq_weighted hκ, integral_eq_integral_Ioi_add_neg hφ,
      setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul] at h0
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hκc)).resolve_left hc
  have hWc : Continuous W := hW.continuous
  have hL1 : ContinuousAt L 1 := by
    simpa using continuousAt_lineProduct h hWc hW' 1
  have hLm1 : ContinuousAt L (-1) := by
    simpa using continuousAt_lineProduct h hWc hW' (-1)
  have hLneg : ContinuousAt (fun t : ℝ => L (-t)) 1 := by
    have : ContinuousAt L (-(1 : ℝ)) := hLm1
    exact this.comp continuous_neg.continuousAt
  have hE1 : E 1 = 0 := by
    refine eq_zero_of_mellin_eq_zero (σ := σ) ?_ (fun y => (hE y).2) (hL1.add hLneg)
    simpa using (hE 0).1
  have hO1 : O 1 = 0 := by
    refine eq_zero_of_mellin_eq_zero (σ := σ) ?_ (fun y => (hO y).2) (hL1.sub hLneg)
    simpa using (hO 0).1
  have hval : L 1 = 0 := by
    have h2 : (2 : ℂ) * L 1 = E 1 + O 1 := by simp only [E, O]; ring
    rw [hE1, hO1, add_zero] at h2
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [← lineProduct_one h W W']
  exact hval


/-! ### Actual restrictions -/

section Actual

open NumberField
open Automorphic HeckeFunctionalEquation
open scoped Classical CategoryTheory.MonObj

variable {F : Type u} [Field F] [NumberField F]

theorem adelicPoint_one (n : ℕ) : adelicPoint F n 1 1 = 1 := by
  unfold adelicPoint
  rw [map_one]
  change (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofInfinite F n 1) = 1
  rw [map_one, map_one]

theorem realPlacePoint_one (n : ℕ) (v : {v : InfinitePlace F // v.IsReal}) :
    realPlacePoint F n v 1 = 1 := by
  rw [realPlacePoint, map_one, adelicPoint_one]

theorem mul_finitePoint_one (n : ℕ) (g : Points F n) : g * finitePoint F n 1 = g := by
  rw [InfiniteWhittakerSlice.finitePoint_one, mul_one]

end Actual

end RealUnequalRankZero

open RealUnequalRankZero NumberField Automorphic HeckeFunctionalEquation ArchimedeanLocal
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (rightDerivative matrixModel)
open scoped Classical CategoryTheory.MonObj

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanRealNMeasurable
  archimedeanRealNBorel

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- With smaller group `GL₁`, a real place admits a pair of actual Whittaker restrictions whose
ordinary unequal-rank integral, for the quotient measure `realQuotientMeasureData 0`, is nonzero
somewhere in every right half-plane. -/
theorem realUnequalOrdinaryPlaceTest_rankZero
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ} (h : 0 < r)
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F 0)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ) (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    (d d' : List RealBlock) (hd : T.realization.HasRealPlaceParameter v d)
    (hd' : T'.realization.HasRealPlaceParameter v d') :
    ∃ (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ)
      (D : RealQuotientMeasureData 0),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realUnequalIntegral h D W W' s ≠ 0 := by
  obtain ⟨A, B, -, hB, ⟨f, hf⟩, hval⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ r T).1 v d hd a ha
  set X := firstRootDirection h
  let fX : realStandardKFinite (r + 1) d :=
    ⟨rightDerivative (matrixModel ℝ (r + 1)) X f,
      Archimedean.rightDerivative_mem_kFiniteFunctions_realStandardModule _ _ f.2 X⟩
  have hBX : B fX = rightDerivative (matrixModel ℝ (r + 1)) X (B f) := hB.2.2.2.2 X f fX rfl
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ := by
    rw [← complex_inverseCharacter]
    exact isStandardAdditiveCharacter_of_unitary _ (inverseCharacter_rational ψ hψ)
  obtain ⟨x', hx'⟩ := cuspidalWhittakerIdentityNonzero F 0 T' ψ.complex⁻¹ hstd'
  let W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ := fun g =>
    cuspWhittaker F T' ψ.complex⁻¹ x' (realPlacePoint F (0 + 1) v g * finitePoint F (0 + 1) 1)
  have hW'act : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' := ⟨x', 1, rfl⟩
  have hWact (g : realStandardKFinite (r + 1) d) :
      IsRealPlaceWhittaker F T ψ.complex v (B g) := by
    refine ⟨A g, 1, ?_⟩
    funext k
    rw [hval, mul_finitePoint_one]
  have hW'mem := ((realPlaceUniformWhittakerModel F ψ hψ 0 T' v a ha d' hd' W').2 hW'act)
  have hW'reg := realUniformWhittakerRegularity 0 d' (-a) W' hW'mem
  have hW'c : Continuous W' := (hW'reg.1 []).2.1.continuous
  have hconv (g : realStandardKFinite (r + 1) d) := by
    have hmem := (realPlaceUniformWhittakerModel F ψ hψ r T v a ha d hd (B g)).1 (hWact g)
    have hreg := realUniformWhittakerRegularity r d a (B g) hmem
    exact realUnequalPairConvergence r 0 h (realQuotientMeasureData 0) a (B g) W'
      hreg.1 hreg.2 hW'reg.1 hW'reg.2
  obtain ⟨σa, hinta, -⟩ := hconv f
  obtain ⟨σb, hintb, -⟩ := hconv fX
  have hint (s : ℂ) (hs : max σa σb < s.re) :
      Integrable (realUnequalIntegrand h (B f) W' s) (realQuotientMeasureData 0).measure :=
    hinta s ((le_max_left _ _).trans_lt hs)
  have hintX (s : ℂ) (hs : max σa σb < s.re) :
      Integrable (realUnequalIntegrand h (rightDerivative (matrixModel ℝ (r + 1)) X (B f)) W' s)
        (realQuotientMeasureData 0).measure := by
    rw [← hBX]
    exact hintb s ((le_max_right _ _).trans_lt hs)
  by_contra hcon
  push Not at hcon
  obtain ⟨σ₁, hz⟩ := hcon (B f) W' (realQuotientMeasureData 0) (hWact f) hW'act
  obtain ⟨σ₂, hzX⟩ := hcon (B fX) W' (realQuotientMeasureData 0) (hWact fX) hW'act
  rw [hBX] at hzX
  have hzero := value_eq_zero_of_integrals_eq_zero h (realQuotientMeasureData 0) (hB.2.1 f)
    (hB.1 f) hW'c hint hintX hz hzX
  have hW'1 : W' 1 = cuspWhittaker F T' ψ.complex⁻¹ x' 1 := by
    change cuspWhittaker F T' ψ.complex⁻¹ x' (realPlacePoint F (0 + 1) v 1 *
      finitePoint F (0 + 1) 1) = _
    rw [mul_finitePoint_one, realPlacePoint_one]
  rw [hf, one_mul, hW'1] at hzero
  exact hx' hzero

/-- `RealUnequalOrdinaryPlaceTestsStatement` restricted to smaller groups `GL_(t+1)` with
`0 < t`. -/
def RealUnequalOrdinaryPlaceTestsPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r), 0 < t →
  ∀ (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' : List RealBlock),
    T.realization.HasRealPlaceParameter v d → T'.realization.HasRealPlaceParameter v d' →
    ∃ (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (D : RealQuotientMeasureData t),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realUnequalIntegral h D W W' s ≠ 0

/-- The positive-rank assertion implies `RealUnequalOrdinaryPlaceTestsStatement`. -/
def RealUnequalOrdinaryPlaceTestsFromPositiveRankStatement : Prop :=
  RealUnequalOrdinaryPlaceTestsPositiveRankStatement.{u} →
    RealUnequalOrdinaryPlaceTestsStatement.{u}

/-- The case `t = 0` is `realUnequalOrdinaryPlaceTest_rankZero`; the other cases are the
premise. -/
theorem realUnequalOrdinaryPlaceTestsFromPositiveRank :
    RealUnequalOrdinaryPlaceTestsFromPositiveRankStatement.{u} := by
  intro hpos F _ _ _ ψ hψ r t h T T' v a ha d d' hd hd'
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact realUnequalOrdinaryPlaceTest_rankZero ψ hψ h T T' v a ha d d' hd hd'
  · exact hpos F ψ hψ r t h ht T T' v a ha d d' hd hd'

end Langlands.Global.RankinSelbergGlobal
