import Langlands.Global.RankinSelberg.ComplexSquareZetaAngularTest
import Langlands.Global.RankinSelberg.ArchimedeanComplexPairFactor
import Langlands.Global.RankinSelberg.ComplexGodementStandardGaussians

/-! # A constant nonzero normalized complex square matrix integral -/

noncomputable section

open MeasureTheory MvPolynomial Set
open scoped ComplexConjugate Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open ArchimedeanLocal
open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.GeneralLinear (UpperEntryPair upperEntryProductMeasure)
open Langlands.GodementJacquet (complexTriangularMatrix)
open ComplexGodement (upperTriangularEntries)
open ComplexGodementGaussianPolynomial (Coordinates coordinates
  standardMatrixTest scalePolynomial standardMatrixTest_eq_squarePolynomialGaussian)
open ComplexCompactProfileFamily (characterList standardSection standardSection_mem standardSection_unitary)
open ComplexSquareFourier (upperMarginal)
open ComplexTateProduct (gammaNormalizer)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.ComplexTate (gaussian zeta_gaussian)
open ArchimedeanComplexPairFactor (complexLFactor_ne_zero)

local instance squareUnitGLMeasurable (j : ℕ) : MeasurableSpace (Langlands.GeneralLinear j ℂ) := borel _
local instance squareUnitGLBorel (j : ℕ) : BorelSpace (Langlands.GeneralLinear j ℂ) := ⟨rfl⟩

variable {n : ℕ}
local notation "I" => Fin n
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix I I ℂ
local notation "Poly" => MvPolynomial (Coordinates n n) ℂ
local notation "Off" => UpperEntryPair n

/-- Each standard square polynomial Gaussian has a Schwartz representative. -/
theorem exists_schwartz_squarePolynomialGaussian (p : Poly) :
    ∃ Φ : 𝓢(Mat, ℂ), (Φ : Mat → ℂ) = squarePolynomialGaussian p := by
  let c : ℂ := Real.sqrt (2 * Real.pi)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  let q := bind₁ (fun j : Coordinates n n => C c⁻¹ * X j) p
  refine ⟨standardMatrixTest q, (standardMatrixTest_eq_squarePolynomialGaussian q).trans ?_⟩
  funext A
  unfold squarePolynomialGaussian
  congr 1
  change aeval (coordinates A) (scalePolynomial q) = aeval (coordinates A) p
  change aeval (coordinates A) (bind₁ (fun j : Coordinates n n => C c * X j) q) = _
  rw [aeval_bind₁]
  change aeval _ (bind₁ (fun j : Coordinates n n => C c⁻¹ * X j) p) = _
  rw [aeval_bind₁]
  congr 2
  funext j
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

private theorem integral_angularScalar (m : ℤ) (u : ℂ) (hu : 0 < u.re) :
    (∫ z, ((Real.pi : ℂ) * gaussian m z) * ComplexTateProduct.additiveWeight m u z) =
      ((Real.pi : ℂ) / 2) * Complex.Gammaℂ (u + (m.natAbs : ℂ) / 2) := by
  have h₀ (z : ℂ) : gaussian m z * ComplexTateProduct.additiveWeight m u z =
      Langlands.LocalFactor.ComplexTate.integrand (gaussian m) m u z := by
    by_cases hz : z = 0
    · simp [hz, ComplexTateProduct.additiveWeight, Langlands.LocalFactor.ComplexTate.integrand]
    · simp [hz, ComplexTateProduct.additiveWeight, Langlands.LocalFactor.ComplexTate.integrand,
        Langlands.LocalFactor.ComplexTate.direction, mul_assoc]
  have hc := zeta_gaussian m hu
  rw [Langlands.LocalFactor.ComplexTate.zeta, Langlands.LocalFactor.ComplexTate.measure,
    integral_smul_measure] at hc
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat] at hc
  simp_rw [mul_assoc, h₀]
  rw [integral_const_mul, ← hc]
  ring

private theorem zeta_angularProduct (w : I → ℤ) (u : I → ℂ) (hu : ∀ j, 0 < (u j).re) :
    ComplexTateProduct.zeta (fun z => ∏ j, (Real.pi : ℂ) * gaussian (w j) (z j)) w u =
      ((Real.pi : ℂ) / 2) ^ n * ∏ j, Complex.Gammaℂ (u j + ((w j).natAbs : ℂ) / 2) := by
  unfold ComplexTateProduct.zeta ComplexTateProduct.integrand
  simp only [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun j z =>
    ((Real.pi : ℂ) * gaussian (w j) z) * ComplexTateProduct.additiveWeight (w j) (u j) z)]
  simp_rw [integral_angularScalar _ _ (hu _)]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The square matrix integral of a compact-finite inducing vector and a standard
polynomial Gaussian, for nondecreasing angular weights, has a constant nonzero normalization. -/
def ComplexSquareZetaUnitStatement : Prop :=
  0 < n → ∀ (μ : Measure G) [μ.IsHaarMeasure] (w : I → ℤ) (p : I → ℂ), Monotone w →
    ∃ (Φ : 𝓢(Mat, ℂ)) (P : Poly) (f : complexStandardKFinite n (characterList w p))
      (c : ℂ) (σ : ℝ),
      (Φ : Mat → ℂ) = squarePolynomialGaussian P ∧ c ≠ 0 ∧
      ∀ s : ℂ, σ < s.re → Integrable (zetaKernel Φ f.val s) μ ∧
        (complexLFactor (characterList w p)).denominator s * (∫ g, zetaKernel Φ f.val s g ∂μ) = c

set_option maxHeartbeats 950000 in
theorem complexSquareZetaUnit : ComplexSquareZetaUnitStatement (n := n) := by
  intro hn μ hμ w p hw
  let ds (i : I) := characterOfParams (w i) (p i)
  let ν : AdditiveHaarMeasure ℂ := ⟨volume, inferInstance, inferInstance⟩
  let : CompactSpace K := ComplexDuality.compactSpace_unitaryCompact n
  let κ : Measure K := Measure.haarMeasure ⊤
  let : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let : IsFiniteMeasure κ := inferInstance
  obtain ⟨P, φ, hφ, hφ₁, hTest⟩ := complexSquareZetaAngularTest w hw
  obtain ⟨Φ, hΦ⟩ := exists_schwartz_squarePolynomialGaussian P
  obtain ⟨c, hc, h⟩ := hTest ν
  let f : complexStandardKFinite n (characterList w p) := ⟨standardSection p φ, standardSection_mem hφ p⟩
  let b (k : K) := f.val k.val
  have hb (k : K) : b k = φ ⟨k.val.val, k.2⟩ := by
    have hK : Unitary.toUnits (⟨k.val.val, k.2⟩ : Matrix.unitaryGroup I ℂ) = k.val := Units.ext rfl
    simpa only [hK] using standardSection_unitary p φ ⟨k.val.val, k.2⟩
  have hbc : Continuous b := f.2.1.1.continuous.comp continuous_subtype_val
  let S (d : I → ℂ) := ∏ j, (Real.pi : ℂ) * gaussian (w j) (d j)
  let J : ℂ := ∫ k, b k * conj (b k) ∂κ
  have hJ : J ≠ 0 := by
    let R (k : K) := Complex.normSq (b k)
    have hR : Continuous R := Complex.continuous_normSq.comp hbc
    have hR₁ : R 1 ≠ 0 := by
      simp only [R, hb, OneMemClass.coe_one, Units.val_one]
      change Complex.normSq (φ 1) ≠ 0
      simp [hφ₁]
    have hPos := hR.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (μ := κ) (HasCompactSupport.of_compactSpace R) (fun _ => Complex.normSq_nonneg _) hR₁
    change (∫ k, b k * conj (b k) ∂κ) ≠ 0
    simp only [Complex.mul_conj, integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr hPos.ne'
  let Q : ℝ≥0 := ComplexTraceFourier.scale 1 ^ Fintype.card Off
  have hQ : (Q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (pow_pos (ComplexTraceFourier.scale_pos 1) _)).ne'
  let C := (Q : ℂ) * c * J
  have hDiag (d : I → ℂ) : upperMarginal 1 (rightAverage κ b hbc Φ) d = C * S d := by
    rw [upperMarginal_rightAverage]
    have hVolume : upperEntryProductMeasure ν n = (volume : Measure (Off → ℂ)) := rfl
    have he (k : K) :
        (∫ z : Off → ℂ, Φ (upperTriangularEntries d z * k.val.val) * b k) =
          (b k * conj (b k)) * (c * S d) := by
      rw [integral_mul_const, ← hVolume]
      change (∫ z : Off → ℂ, Φ (complexTriangularMatrix d z * k.val.val)
        ∂upperEntryProductMeasure ν n) * b k = _
      simp only [hΦ]
      rw [h d k, hb]
      ring
    simp_rw [he]
    rw [integral_mul_const]
    change (Q : ℂ) * (J * (c * S d)) = _
    dsimp only [C]
    ring
  obtain ⟨m, hm⟩ := complexSquareZetaConvergence hn ds
  obtain ⟨cH, hcH, hRaw⟩ := complexSquareZetaProductTate μ κ 1 hμ inferInstance
  obtain ⟨bL, hbL⟩ := complexLFactor_ne_zero (characterList w p)
  obtain ⟨bP, hbP⟩ := (finite_range fun j : I => -(p j).re).bddAbove
  let b₀ := max (max bL bP) ((n : ℝ) + m + |(((n : ℂ) - 1) / 2).re|)
  let c₀ := (cH : ℂ) * C * ((Real.pi : ℂ) / 2) ^ n
  refine ⟨Φ, P, f, c₀, b₀, hΦ, ?_, fun s hs => ?_⟩
  · exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr hcH).ne')
      (mul_ne_zero (mul_ne_zero hQ hc) hJ))
      (pow_ne_zero _ (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero))
  have hi : Integrable (zetaKernel Φ f.val s) μ := by
    apply hm μ Φ f.val f.2.1 s
    rw [Complex.add_re]
    have h := (le_max_right (max bL bP) _).trans_lt hs
    linarith [neg_abs_le (((n : ℂ) - 1) / 2).re]
  have hPos (j : I) : 0 < (s + p j).re := by
    rw [Complex.add_re]
    have h := (hbP (mem_range_self j)).trans_lt
      ((le_max_right bL bP).trans_lt ((le_max_left (max bL bP) _).trans_lt hs))
    linarith
  refine ⟨hi, ?_⟩
  have hsL := hbL s ((le_max_left bL bP).trans_lt ((le_max_left (max bL bP) _).trans_lt hs))
  have hz := hRaw ds Φ f.val f.2.1 s hi
  change (∫ g, zetaKernel Φ f.val s g ∂μ) = (cH : ℂ) *
    ComplexTateProduct.zeta (upperMarginal 1 (rightAverage κ b hbc Φ)) (fun j => (ds j).weight)
      (fun j => s + (ds j).exponent) at hz
  rw [hz]
  simp only [ds, characterOfParams_weight, characterOfParams_exponent]
  have hZ : ComplexTateProduct.zeta (upperMarginal 1 (rightAverage κ b hbc Φ)) w (fun j => s + p j) =
      C * ComplexTateProduct.zeta S w (fun j => s + p j) := by
    unfold ComplexTateProduct.zeta ComplexTateProduct.integrand
    simp_rw [hDiag, mul_assoc, integral_const_mul]
  rw [hZ, zeta_angularProduct w _ hPos]
  let L := (complexLFactor (characterList w p)).denominator s
  have hL : L = (∏ j : I, Complex.Gammaℂ (s + p j + ((w j).natAbs : ℂ) / 2))⁻¹ := by
    change (complexLFactor (List.ofFn ds)).denominator s = _
    rw [denominator_complexLFactor_ofFn, ← Finset.prod_inv_distrib]
    rfl
  have hGamma : (∏ j : I, Complex.Gammaℂ (s + p j + ((w j).natAbs : ℂ) / 2)) ≠ 0 := by
    intro he
    exact hsL (hL.trans (by rw [he, inv_zero]))
  let H := ∏ j : I, Complex.Gammaℂ (s + p j + ((w j).natAbs : ℂ) / 2)
  change L * ((cH : ℂ) * (C * (((Real.pi : ℂ) / 2) ^ n * H))) = c₀
  rw [hL]
  change H⁻¹ * ((cH : ℂ) * (C * (((Real.pi : ℂ) / 2) ^ n * H))) = c₀
  calc
    _ = c₀ * (H⁻¹ * H) := by dsimp only [c₀]; ring
    _ = c₀ := by rw [inv_mul_cancel₀ hGamma, mul_one]

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
