import Langlands.Global.RankinSelberg.RealLocalEqualSquareLimit
import Langlands.Global.RankinSelberg.RealLocalEqualGeneratorFamily
import Langlands.Global.RankinSelberg.RealLocalEqualNormalizedFactors
import Langlands.Global.RankinSelberg.RealLocalEqualDualUnfolding
import Langlands.Global.RankinSelberg.RealLocalEqualSquareFourier
import Langlands.Analysis.Complex.AffineTraceRecovery

/-! # Recovery of the real equal-rank normalized equation for column generators -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) :=
  ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedAddCommGroup (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedSpace ℂ (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedSpace

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

/-! ### Generators and recursive coefficients -/

/-- The value at `-1` of a real character, raised to the power `t + 1`, squares to one. -/
theorem character_minusOne_pow_mul_self (d : RealCharacterData) :
    ((d.character (-1) : ℂ) ^ (t + 1)) * ((d.character (-1) : ℂ) ^ (t + 1)) = 1 := by
  rw [← pow_add, ← Nat.two_mul, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow]
  norm_num

/-- The column generator is a fixed positive multiple of the equal-rank recursive
coefficient of `RealLocalEqualUnfolding`, times the character sign `d(-1)^(t+1)`. -/
theorem godementLeadingFamily_eq_recursive (D : RealQuotientMeasureData t) (b : ℝˣ)
    (Φ : 𝓢(X, ℂ)) {ds : List RealBlock} {U : G → ℂ}
    (hU : U ∈ realUniformWhittakerModel t ds (-b)) :
    ∃ s₀ : ℝ≥0, 0 < s₀ ∧ ∀ (p : Fin 2) (z : ℂ) (g : H),
      godementLeadingFamily D b Φ U p g z =
        (s₀ : ℂ) * (((charData p z).character (-1) : ℂ) ^ (t + 1)) *
          equalRecursiveCoefficient b D Φ U (kernelWhittakerLaw_of_mem_model hU) (charData p z) g := by
  obtain ⟨s₀, hs₀, _, hq⟩ := realGodementColumnQuotient t b D
  refine ⟨s₀, hs₀, fun p z g => ?_⟩
  have h := (hq Φ ds U (charData p z) (weylLong (t + 2) ℝ * g) hU).2.2
  have hC := character_minusOne_pow_mul_self (t := t) (charData p z)
  unfold godementLeadingFamily godementColumnValue equalRecursiveCoefficient
  rw [h]
  calc
    _ = (s₀ : ℂ) * ((((charData p z).character (-1) : ℂ) ^ (t + 1)) *
          (((charData p z).character (-1) : ℂ) ^ (t + 1))) *
        ∫ q, quotientKernel b Φ U (kernelWhittakerLaw_of_mem_model hU) (charData p z)
          (weylLong (t + 2) ℝ * g) q ∂D.measure := by rw [hC, mul_one]
    _ = _ := by ring

/-- The equal-rank integral is linear in the first coefficient. -/
theorem realEqualIntegral_const_mul (D' : RealQuotientMeasureData (t + 1)) (c : ℂ) (R V : H → ℂ)
    (φ : (Fin (t + 2) → ℝ) → ℂ) (s : ℂ) :
    realEqualIntegral D' (fun g => c * R g) V φ s = c * realEqualIntegral D' R V φ s := by
  unfold realEqualIntegral ArchimedeanLocal.equalIntegral ArchimedeanLocal.equalIntegrand
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  ring

/-- The dual equal-rank integral is linear in the first coefficient. -/
theorem realEqualDualIntegral_const_mul (b : ℝˣ) (D' : RealQuotientMeasureData (t + 1)) (c : ℂ)
    (R V : H → ℂ) (φ : (Fin (t + 2) → ℝ) → ℂ) (s : ℂ) :
    realEqualDualIntegral b D' (fun g => c * R g) V φ s = c * realEqualDualIntegral b D' R V φ s := by
  unfold realEqualDualIntegral ArchimedeanLocal.equalIntegral ArchimedeanLocal.equalIntegrand
    ArchimedeanLocal.dualFunction
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  ring

/-- A real pair `ε`-factor, viewed as a function of `1 - s`, is bounded on vertical strips. -/
theorem stripGrowth_realPairEpsilon_reflect (xs ys : List RealBlock) (b : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) (z : ℂ) :
    HasStripExponentialGrowth (fun s => (realPairEpsilon xs ys b c hc (1 - s + z) : ℂ)) := by
  intro l u
  let k : ℝ := ((realRank xs * realRank ys : ℕ) : ℝ)
  let e₀ : ℂ := (realPairEpsilon xs ys b c hc 0 : ℂ)
  have hb : 0 < |(b : ℝ)| := abs_pos.mpr b.ne_zero
  let M : ℝ := max |1 - l + z.re| |1 - u + z.re|
  refine ⟨‖e₀‖ * Real.exp (abs (Real.log |(b : ℝ)|) * (k * M)), 0, 0, by positivity, le_rfl,
    fun s hl hu _ => ?_⟩
  show ‖(realPairEpsilon xs ys b c hc (1 - s + z) : ℂ)‖ ≤ _
  rw [zero_mul, Real.exp_zero, mul_one, realPairEpsilon_eq_at_zero_mul_cpow, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hb]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : ((((realRank xs * realRank ys : ℕ) : ℂ) * (1 - s + z))).re = k * (1 - s.re + z.re) := by
    simp [k]
  rw [hre, Real.rpow_def_of_pos hb]
  refine Real.exp_le_exp.mpr ?_
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hM : |1 - s.re + z.re| ≤ M := by
    rcases le_total 0 (1 - s.re + z.re) with h | h
    · rw [abs_of_nonneg h]
      exact (le_abs_self _).trans' (by linarith) |>.trans (le_max_left _ _)
    · rw [abs_of_nonpos h]
      exact (neg_le_abs _).trans' (by linarith) |>.trans (le_max_right _ _)
  calc
    Real.log |(b : ℝ)| * (k * (1 - s.re + z.re)) ≤
        abs (Real.log |(b : ℝ)|) * |k * (1 - s.re + z.re)| :=
      (le_abs_self _).trans (abs_mul _ _).le
    _ ≤ abs (Real.log |(b : ℝ)|) * (k * M) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_mul, abs_of_nonneg hk]
      exact mul_le_mul_of_nonneg_left hM hk


theorem charData_character_neg_one (e : Fin 2) (z : ℂ) :
    ((charData e z).character (-1) : ℂ) = (-1 : ℂ) ^ e.val := by
  rw [(charData e z).character_eq]
  change (((((-1 : ℝˣ) : ℝ) / |((-1 : ℝˣ) : ℝ)| : ℝ)) : ℂ) ^ e.val *
    ((|((-1 : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ z = (-1 : ℂ) ^ e.val
  simp

private theorem stripGrowth_reflect' {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) :
    HasStripExponentialGrowth (fun s => f (1 - s)) := by
  intro l u
  obtain ⟨C, K, T, hC, hK, hb⟩ := hf (1 - u) (1 - l)
  refine ⟨C, K, T, hC, hK, fun s hl hu hT => ?_⟩
  have him : |(1 - s).im| = |s.im| := by
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have h := hb (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith) (him ▸ hT)
  rwa [him] at h

private theorem stripGrowth_const' (c : ℂ) : HasStripExponentialGrowth (fun _ => c) :=
  fun _ _ => ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩

/-! ### The generator trace -/

variable (t) in
/-- For one of the column generators `L(z) = godementLeadingFamily D (-a) Φ U e · z`
with a compactly supported full-row-rank test `Φ` and `U` in the uniform model of a real
character list `cs` with character `a`, and the larger coefficient `B f`: assuming the
normalized corank-one equation for all larger coefficients paired with `U`, the normalized
matrix equation for all orthogonal-finite square tests, and a continuous Whittaker evaluation
of `B`, the real equal-rank integral of `(L(z), B f, φ)` and its dual satisfy the entire
normalized equal-rank equation with strip growth, for every leading exponent `z`. -/
def RealLocalEqualGeneratorTraceStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ) (e : Fin 2)
    (cs fs : List RealCharacterData), cs.length = t + 1 → fs.length = t + 2 →
  ∀ (U : G → ℂ), U ∈ realUniformWhittakerModel t (cs.map RealBlock.character) a →
  ∀ (B : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
    IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B →
    (∃ L : DerivativeSmoothVectors (matrixModel ℝ (t + 2))
        (RealStandardCompactBanach.representation (n := t + 2) (fs.map RealBlock.character)) →L[ℂ] ℂ,
      RealStandardCompactBanach.IsWhittakerStandardEvaluation (fs.map RealBlock.character) (-a) B L) →
  ∀ (f : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character))
    (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
  ∀ (Φ : 𝓢(X, ℂ)), (∀ x ∉ S, Φ x = 0) → ∀ (φ : 𝓢(Fin (t + 2) → ℝ, ℂ)),
    (∀ V ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a),
      RealJacquet.HasRealPairNormalizedGrowth (fs.map RealBlock.character) (cs.map RealBlock.character)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock)
        ((cs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
        ((RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ) ^ (t + 1) *
          (RealJacquet.determinant (cs.map RealBlock.character) (-1) : ℂ))
        (realUnequalIntegral (Nat.lt_succ_self t) D V U)
        (realUnequalDualIntegral (Nat.lt_succ_self t) (-a) D V U)) →
    (∀ Ψ : 𝓢(Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ, ℂ),
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ (t + 2) =>
        fun X' : Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ => Ψ (k.val⁻¹.val * X'))) →
      RealMatrixCoefficientNormalizedGrowth t D' a e (fs.map RealBlock.character) f Ψ
        [RealBlock.character (charData e 0)] (fs.map RealBlock.character)
        ([RealBlock.character (charData e 0)].map RealLocalJacquet.dualBlock)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) (-a)
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1) →
    ∀ z : ℂ,
      RealJacquet.HasRealPairNormalizedGrowth
        (RealBlock.character (charData e z) :: cs.map RealBlock.character) (fs.map RealBlock.character)
        ((RealBlock.character (charData e z) :: cs.map RealBlock.character).map
          RealLocalJacquet.dualBlock)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) (-a)
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
        ((RealJacquet.determinant (RealBlock.character (charData e z) :: cs.map RealBlock.character)
          (-1) : ℂ) ^ (t + 1))
        (realEqualIntegral D' (fun g => godementLeadingFamily D (-a) Φ U e g z) (B f) φ)
        (realEqualDualIntegral (-a) D' (fun g => godementLeadingFamily D (-a) Φ U e g z) (B f) φ)


set_option maxHeartbeats 4000000 in
theorem realLocalEqualGeneratorTrace : RealLocalEqualGeneratorTraceStatement t := by
  intro D D' a e cs fs hcs hfs U hU B hB hL f S hS hRank Φ hΦ φ hAdj hMat u
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  set c : ℝ≥0 := NNReal.sqrt ‖(a : ℝ)‖₊ with hc_def
  have hc : 0 < c := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
  set signA : ℂ := (RealJacquet.determinant es (-1) : ℂ) ^ (t + 1) *
    (RealJacquet.determinant ds (-1) : ℂ) with hsignA
  have hsA : signA ≠ 0 := mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)
  set χ0 : RealBlock := RealBlock.character (charData e 0) with hχ0_def
  let Ψ : 𝓢(Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ, ℂ) := equalSquareSchwartz Φ φ
  have hΨ : (Ψ : Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ → ℂ) = equalSquareTest Φ φ :=
    funext (equalSquareSchwartz_apply Φ φ)
  obtain ⟨τ, σ, τd, σd, hR5⟩ := realLocalEqualSquareLimit D D' a e cs fs hcs hfs U hU B hB hL f
    es ds (es.map RealLocalJacquet.dualBlock) (ds.map RealLocalJacquet.dualBlock) a c hc signA hsA hAdj
    [χ0] es ([χ0].map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) (-a) c hc 1
    one_ne_zero hMat
  obtain ⟨A, hAcurve, hAgrowth, hAprimal, hAdual⟩ := hR5 Ψ
  have hV : B f ∈ realUniformWhittakerModel (t + 1) es (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  obtain ⟨τ₁, σ₁, hJ₁⟩ := exists_uniformModel_equalKernel_chamber D D' a ds es hU hV
  have hUd := RealUniformWhittakerDual.realUniformWhittakerCharacterDual t cs hcs a U hU
  have hVd := RealUniformWhittakerDual.realUniformWhittakerCharacterDual (t + 1) fs hfs (-a) (B f) hV
  obtain ⟨τ₂, σ₂, hJ₂⟩ := exists_uniformModel_equalKernel_chamber D D' (-a)
    (RealUniformWhittakerDual.dualCharacterBlocks cs) (RealUniformWhittakerDual.dualCharacterBlocks fs)
    hUd hVd
  have hU' : U ∈ realUniformWhittakerModel t ds (-(-a)) := by rwa [neg_neg]
  obtain ⟨s₀, hs₀, hrel⟩ := godementLeadingFamily_eq_recursive D (-a) Φ hU'
  obtain ⟨scale, hscale, hμ, -⟩ := realGodementColumnQuotient (t + 1) (-a) D'
  have hUlaw : KernelWhittakerLaw (-a) U := kernelWhittakerLaw_of_mem_model hU'
  have hVlaw : KernelWhittakerLaw (-(-a)) (B f) := by
    rw [neg_neg]
    exact kernelWhittakerLaw_of_mem_model hV
  set Csgn : ℂ := ((-1 : ℂ) ^ e.val) ^ (t + 1) with hCsgn
  have hCz (z : ℂ) : ((charData e z).character (-1) : ℂ) ^ (t + 1) = Csgn := by
    rw [charData_character_neg_one]
  have hC0 : Csgn ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  have hs0 : (s₀ : ℂ) ≠ 0 := by exact_mod_cast hs₀.ne'
  have hsc : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale.ne'
  set κ : ℂ := (scale : ℂ) * ((s₀ : ℂ) * Csgn)⁻¹ with hκ_def
  have hκ : κ ≠ 0 := mul_ne_zero hsc (inv_ne_zero (mul_ne_zero hs0 hC0))
  set κd : ℂ := Csgn⁻¹ * κ with hκd_def
  have hκd : κd ≠ 0 := mul_ne_zero (inv_ne_zero hC0) hκ
  let L (z : ℂ) : H → ℂ := fun g => godementLeadingFamily D (-a) Φ U e g z
  let R (z : ℂ) : H → ℂ := equalRecursiveCoefficient (-a) D Φ U hUlaw (charData e z)
  have hLR (z : ℂ) : R z = fun g => ((s₀ : ℂ) * Csgn)⁻¹ * L z g := by
    funext g
    have h := hrel e z g
    rw [hCz z] at h
    change L z g = (s₀ : ℂ) * Csgn * R z g at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 hC0), one_mul]
  have hIL (z s : ℂ) : realEqualIntegral D' (R z) (B f) φ s =
      ((s₀ : ℂ) * Csgn)⁻¹ * realEqualIntegral D' (L z) (B f) φ s := by
    rw [hLR z, realEqualIntegral_const_mul]
  have hIdL (z s : ℂ) : realEqualDualIntegral (-a) D' (R z) (B f) φ s =
      ((s₀ : ℂ) * Csgn)⁻¹ * realEqualDualIntegral (-a) D' (L z) (B f) φ s := by
    rw [hLR z, realEqualDualIntegral_const_mul]
  let dA := (realPairLFactor es ds).denominator
  let dM := (realPairLFactor [χ0] es).denominator
  let dAd := (realPairLFactor (es.map RealLocalJacquet.dualBlock)
    (ds.map RealLocalJacquet.dualBlock)).denominator
  let dMd := (realPairLFactor ([χ0].map RealLocalJacquet.dualBlock)
    (es.map RealLocalJacquet.dualBlock)).denominator
  let Ph (z w : ℂ) : ℂ := signA * (realPairEpsilon es ds a c hc w : ℂ) *
    (1 * (realPairEpsilon [χ0] es (-a) c hc (w + z) : ℂ))
  have hPh (z w : ℂ) : Ph z w ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsA (Units.ne_zero _)) (mul_ne_zero one_ne_zero (Units.ne_zero _))
  let Z (x : ℂ × ℂ) : ℂ := κ * (dA x.2 * dM (x.2 + x.1) * realEqualIntegral D' (L x.1) (B f) φ x.2)
  let Zd (x : ℂ × ℂ) : ℂ := (Ph x.1 (1 - x.2))⁻¹ *
    (dAd x.2 * dMd (x.2 - x.1) * (κd * realEqualDualIntegral (-a) D' (L x.1) (B f) φ x.2))
  have hPrim (z : ℂ) (hz : z ∈ {z : ℂ | max τ τ₁ < z.re}) (s : ℂ) (hs : max σ σ₁ < s.re) :
      A (z, s) = Z (z, s) := by
    have hJ := hJ₁ e Ψ z s ((le_max_right _ _).trans_lt hz) ((le_max_right _ _).trans_lt hs)
    rw [hΨ] at hJ
    obtain ⟨-, hunf⟩ := realLocalEqualUnfolding (-a) D D' scale hscale hμ Φ φ U hUlaw (B f)
      (charData e z) s hVlaw hJ
    rw [hAprimal z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs), hΨ, ← hunf]
    change dA s * dM (s + z) * ((scale : ℂ) * realEqualIntegral D' (R z) (B f) φ s) = Z (z, s)
    rw [hIL]
    simp only [Z, hκ_def]
    ring
  have hFΨ : (realRectangularSchwartzFourier (-a) Ψ : Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ → ℂ) =
      equalSquareTest (realRectangularSchwartzFourier (-a) Φ) (realFourierTransform (-a) φ) :=
    funext (realLocalEqualSquareFourier (-a) Φ φ)
  have hDual (z : ℂ) (hz : z ∈ {z : ℂ | max τd τ₂ < (-z).re}) (s : ℂ) (hs : max σd σ₂ < s.re) :
      A (z, 1 - s) = Zd (z, s) := by
    have hJ := hJ₂ e (realRectangularSchwartzFourier (-a) Ψ) (-z) s
      ((le_max_right _ _).trans_lt hz) ((le_max_right _ _).trans_lt hs)
    rw [hFΨ, ← charData_inverse e z] at hJ
    obtain ⟨-, hunf⟩ := realLocalEqualDualUnfolding (-a) D D' scale hscale hμ Φ φ U hUlaw (B f)
      (charData e z) s hVlaw hJ
    have hA := hAdual z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)
    rw [hFΨ, ← charData_inverse e z] at hA
    set J := ∫ p, equalUnfoldedKernel (charData e z).inverse
      (equalSquareTest (realRectangularSchwartzFourier (-a) Φ) (realFourierTransform (-a) φ))
      (ArchimedeanLocal.dualFunction (t + 1) U) (ArchimedeanLocal.dualFunction (t + 2) (B f)) s p
        ∂(D.measure.prod D'.groupHaar) with hJ_def
    have hJeq : J = κd * realEqualDualIntegral (-a) D' (L z) (B f) φ s := by
      have h2 := hunf
      change (scale : ℂ) * realEqualDualIntegral (-a) D' (R z) (B f) φ s =
        ((charData e z).character (-1) : ℂ) ^ (t + 1) * J at h2
      rw [hIdL, hCz z] at h2
      calc
        J = Csgn⁻¹ * (Csgn * J) := by rw [← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
        _ = Csgn⁻¹ * ((scale : ℂ) * (((s₀ : ℂ) * Csgn)⁻¹ *
              realEqualDualIntegral (-a) D' (L z) (B f) φ s)) := by rw [h2]
        _ = _ := by simp only [hκd_def, hκ_def]; ring
    have hA' : Ph z (1 - s) * A (z, 1 - s) = dAd s * dMd (s - z) * J := hA
    calc
      A (z, 1 - s) = (Ph z (1 - s))⁻¹ * (Ph z (1 - s) * A (z, 1 - s)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (hPh _ _), one_mul]
      _ = (Ph z (1 - s))⁻¹ * (dAd s * dMd (s - z) * J) := by rw [hA']
      _ = Zd (z, s) := by rw [hJeq]
  have hEpsA : Differentiable ℂ (fun w : ℂ => (realPairEpsilon es ds a c hc w : ℂ)) :=
    differentiable_realEpsilon (realPairBlocks es ds) a c hc
  have hEpsM : Differentiable ℂ (fun w : ℂ => (realPairEpsilon [χ0] es (-a) c hc w : ℂ)) :=
    differentiable_realEpsilon (realPairBlocks [χ0] es) (-a) c hc
  have hPhd : Differentiable ℂ (fun x : ℂ × ℂ => Ph x.1 (1 - x.2)) :=
    ((differentiable_const signA).mul (hEpsA.comp ((differentiable_const 1).sub differentiable_snd))).mul
      ((differentiable_const 1).mul (hEpsM.comp (((differentiable_const 1).sub differentiable_snd).add
        differentiable_fst)))
  have hHol (Rr : ℝ) : ∃ σg : ℝ,
      DifferentiableOn ℂ Z (Metric.ball (0 : ℂ) Rr ×ˢ {s : ℂ | σg < s.re}) ∧
      DifferentiableOn ℂ Zd (Metric.ball (0 : ℂ) Rr ×ˢ {s : ℂ | σg < s.re}) := by
    obtain ⟨σg, -, hd₁, hd₂⟩ := realLocalEqualGeneratorFamily D D' (-a) (-a) ds es U hU' (B f) hV e
      S hS hRank Φ hΦ φ Rr
    refine ⟨σg, ?_, ?_⟩
    · exact ((((realPairLFactor es ds).entire.comp differentiable_snd).mul
        ((realPairLFactor [χ0] es).entire.comp (differentiable_snd.add differentiable_fst))).differentiableOn.mul
          hd₁).const_mul κ
    · exact (hPhd.inv fun x => hPh _ _).differentiableOn.mul
        ((((realPairLFactor _ _).entire.comp differentiable_snd).mul
          ((realPairLFactor _ _).entire.comp (differentiable_snd.sub differentiable_fst))).differentiableOn.mul
            (hd₂.const_mul κd))
  have hSo : IsOpen {z : ℂ | max τ τ₁ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hSdo : IsOpen {z : ℂ | max τd τ₂ < (-z).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_neg)
  have hSne : ({z : ℂ | max τ τ₁ < z.re} : Set ℂ).Nonempty :=
    ⟨((max τ τ₁ + 1 : ℝ) : ℂ), show max τ τ₁ < ((max τ τ₁ + 1 : ℝ) : ℂ).re by
      rw [Complex.ofReal_re]; linarith⟩
  have hSdne : ({z : ℂ | max τd τ₂ < (-z).re} : Set ℂ).Nonempty :=
    ⟨-((max τd τ₂ + 1 : ℝ) : ℂ), show max τd τ₂ < (-(-((max τd τ₂ + 1 : ℝ) : ℂ))).re by
      rw [neg_neg, Complex.ofReal_re]; linarith⟩
  obtain ⟨θ, hθ⟩ := Langlands.Analysis.affineTraceRecovery A Z Zd _ _ (max σ σ₁) (max σd σ₂) hSo hSdo
    hSne hSdne hAcurve hHol (fun z hz s hs => hPrim z hz s hs) (fun z hz s hs => hDual z hz s hs) u
  have hd : realRank ds = t + 1 := by
    show realRank (cs.map RealBlock.character) = t + 1
    rw [Langlands.Archimedean.realRank_map_character, hcs]
  have he : realRank es = t + 2 := by
    show realRank (fs.map RealBlock.character) = t + 2
    rw [Langlands.Archimedean.realRank_map_character, hfs]
  unfold RealJacquet.HasRealPairNormalizedGrowth
  refine ⟨fun s => κ⁻¹ * A (u, s), fun s => κd⁻¹ * (Ph u (1 - s) * A (u, 1 - s)), ?_, ?_, ?_, ?_,
    ⟨θ, fun s hs => ?_⟩, fun s => ?_⟩
  · exact (hAcurve (fun s => (u, s)) ((differentiable_const u).prodMk differentiable_id)).const_mul _
  · exact ((hPhd.comp ((differentiable_const u).prodMk differentiable_id)).mul
      (hAcurve (fun s => (u, 1 - s)) ((differentiable_const u).prodMk
        ((differentiable_const 1).sub differentiable_id)))).const_mul _
  · exact (stripGrowth_const' κ⁻¹).mul (hAgrowth u)
  · have hεA : HasStripExponentialGrowth (fun s => (realPairEpsilon es ds a c hc (1 - s) : ℂ)) := by
      simpa only [add_zero] using stripGrowth_realPairEpsilon_reflect es ds a c hc 0
    exact (stripGrowth_const' κd⁻¹).mul ((((stripGrowth_const' signA).mul hεA).mul
      ((stripGrowth_const' 1).mul (stripGrowth_realPairEpsilon_reflect [χ0] es (-a) c hc u))).mul
        (stripGrowth_reflect' (hAgrowth u)))
  · obtain ⟨h₁, h₂⟩ := hθ s hs
    refine ⟨?_, ?_⟩
    · beta_reduce
      rw [h₁]
      simp only [Z]
      rw [← mul_assoc, inv_mul_cancel₀ hκ, one_mul, ← RealJacquet.realPairLFactor_equal_pair e u ds fs s]
    · beta_reduce
      rw [h₂]
      simp only [Zd]
      rw [← mul_assoc (Ph u (1 - s)), mul_inv_cancel₀ (hPh _ _), one_mul]
      have hlists : (RealBlock.character (charData e u) :: ds).map RealLocalJacquet.dualBlock =
          RealBlock.character (charData e (-u)) :: ds.map RealLocalJacquet.dualBlock := by
        simp only [List.map_cons, RealJacquet.dualBlock_charData]
      have hχd : [χ0].map RealLocalJacquet.dualBlock = [RealBlock.character (charData e 0)] := by
        simp only [hχ0_def, List.map_cons, List.map_nil, RealJacquet.dualBlock_charData, neg_zero]
      have hesd : es.map RealLocalJacquet.dualBlock =
          (fs.map RealCharacterData.inverse).map RealBlock.character :=
        RealJacquet.map_dualBlock_character fs
      have hden : dAd s * dMd (s - u) =
          (realPairLFactor ((RealBlock.character (charData e u) :: ds).map RealLocalJacquet.dualBlock)
            (es.map RealLocalJacquet.dualBlock)).denominator s := by
        simp only [dAd, dMd]
        rw [hlists, hχd, hesd, sub_eq_add_neg]
        exact RealJacquet.realPairLFactor_equal_pair e (-u) (ds.map RealLocalJacquet.dualBlock)
          (fs.map RealCharacterData.inverse) s
      rw [← hden]
      calc
        κd⁻¹ * (dAd s * dMd (s - u) * (κd * realEqualDualIntegral (-a) D' (L u) (B f) φ s)) =
            (κd⁻¹ * κd) * (dAd s * dMd (s - u) * realEqualDualIntegral (-a) D' (L u) (B f) φ s) := by
          ring
        _ = _ := by rw [inv_mul_cancel₀ hκd, one_mul]
  · have hshift := RealJacquet.realPairEpsilon_charData_shift e u fs (-a) c hc s
    have hcomm := congrArg (fun x : ℂˣ => (x : ℂ)) (CuspidalPairPartialGammaGlobal.realPairEpsilon_comm es ds a c hc s)
    have hcoef := RealJacquet.equal_epsilon_coefficient (r := t) (charData e u) ds es hd he a c hc s
    rw [hCz u] at hcoef
    change κd⁻¹ * (Ph u (1 - (1 - s)) * A (u, 1 - (1 - s))) = _ * _ * (κ⁻¹ * A (u, s))
    rw [sub_sub_cancel]
    change κd⁻¹ * ((signA * (realPairEpsilon es ds a c hc s : ℂ) *
      (1 * (realPairEpsilon [χ0] es (-a) c hc (s + u) : ℂ))) * A (u, s)) = _
    rw [← hshift, hcomm, ← hcoef]
    simp only [hκd_def, hsignA]
    field_simp
    ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
