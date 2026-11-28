import Langlands.Global.RankinSelberg.RealSquareZetaPolynomial
import Langlands.Global.RankinSelberg.RealAdjacentGaussianSplit
import Langlands.Global.RankinSelberg.RealAdjacentSquareGrowth

/-! # Polynomial normalization of compactly paired real square tests -/

noncomputable section

open MeasureTheory MvPolynomial Set
open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealSquarePolynomialGaussian

open ArchimedeanLocal Langlands.Archimedean Langlands.GeneralLinear Langlands.GodementJacquet
open ArchimedeanDeterminantTheta (torusL)
open Langlands.Archimedean.InductionStages (integral_mem)
open RealGodementGaussianPolynomial (Coordinates coordinates matrixGaussian matrixSqNorm gaussianPolynomial_apply)
open RealJacquet (exists_leftTranslate_gaussianPolynomial matrixSqNorm_orthogonal_mul
  realAdjacentMatrixWeight realMatrixZetaKernel_detCharacter)
open RealPrincipalSeries (realMatrixHeight_unitary_mul exists_uniform_principalSeries_derivative_height
  twistedPositionList realDetCharacter realDetCharacter_mul_mem_principalSeries
  realPositionCharacter_twistedPositionList realPositionSign_twistedPositionList
  realPositionExponent_twistedPositionList realDetCharacter_mul realDetCharacter_ne_zero)
open Langlands.Archimedean.RealBlockPosition (realPositionSign realPositionCharacter_eq_charFun)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel

private local instance (j : ℕ) : LocallyCompactSpace (Matrix (Fin j) (Fin j) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin j → Fin j → ℝ))
private local instance (j : ℕ) : LocallyCompactSpace (GeneralLinear j ℝ) :=
  Units.isOpenEmbedding_val.locallyCompactSpace
private local instance (j : ℕ) : SecondCountableTopology (GeneralLinear j ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

variable {r : ℕ}
local notation "n" => r + 1
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "G" => GeneralLinear n ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "Poly" => MvPolynomial (Coordinates n n) ℂ
local notation "D" => ArchimedeanLocal.detPower realNormalizedAbs

private def squareGaussianLinear : Poly →ₗ[ℂ] (Mat → ℂ) where
  toFun := squarePolynomialGaussian
  map_add' P Q := by
    funext A
    simp only [squarePolynomialGaussian, map_add, Pi.add_apply, add_mul]
  map_smul' z P := by
    funext A
    simp only [squarePolynomialGaussian, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

private abbrev squareDegreeSpace (P : Poly) : Submodule ℂ (Mat → ℂ) :=
  (restrictTotalDegree (Coordinates n n) ℂ P.totalDegree).map squareGaussianLinear

private theorem left_mem_squareDegreeSpace (P : Poly) {k : G} (hk : k ∈ Kc) :
    (fun A => squarePolynomialGaussian P (k.val * A)) ∈ squareDegreeSpace P := by
  obtain ⟨Q, hQ, h⟩ := exists_leftTranslate_gaussianPolynomial P hk
  refine ⟨Q, hQ, funext fun A => ?_⟩
  have hA := h A
  simp only [gaussianPolynomial_apply] at hA
  have hG : matrixGaussian (k.val * A) = matrixGaussian A := by
    simp only [matrixGaussian, matrixSqNorm_orthogonal_mul A hk]
  rw [hG] at hA
  have hP := mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne' : matrixGaussian A ≠ 0) hA
  change squarePolynomialGaussian Q A = squarePolynomialGaussian P (k.val * A)
  simp only [squarePolynomialGaussian, matrixSqNorm_orthogonal_mul A hk, hP]

variable {K : Type*} [Group K]

/-- The inverse left orthogonal translates of a standard square test span a finite-dimensional space. -/
theorem finiteDimensional_leftSquareGaussian (i : K →* G) (hi : ∀ k, i k ∈ Kc)
    (P : Poly) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K =>
      fun A : Mat => squarePolynomialGaussian P ((i k)⁻¹.val * A))) := by
  apply Submodule.finiteDimensional_of_le (S₂ := squareDegreeSpace P)
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact left_mem_squareDegreeSpace P ((unitaryCompact ℝ n).inv_mem (hi k))

variable [TopologicalSpace K] [MeasurableSpace K]

section CompactPairing

variable [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K]

omit [IsTopologicalGroup K] in
private theorem exists_squareGaussian_leftAverage (i : K →* G) (hi : Continuous i)
    (hK : ∀ k, i k ∈ Kc) (ν : Measure K) [IsFiniteMeasure ν] (w : K → ℂ) (hw : Continuous w)
    (Φ : 𝓢(Mat, ℂ)) (P : Poly) (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) :
    ∃ Q : Poly, ∀ A, squarePolynomialGaussian Q A = ∫ k, w k * Φ ((i k)⁻¹.val * A) ∂ν := by
  let V := squareDegreeSpace P
  let a (k : K) (A : Mat) := w k * Φ ((i k)⁻¹.val * A)
  have hV (k : K) : a k ∈ V := by
    change w k • (fun A : Mat => Φ ((i k)⁻¹.val * A)) ∈ V
    rw [hΦ]
    exact Submodule.smul_mem V _ (left_mem_squareDegreeSpace P ((unitaryCompact ℝ n).inv_mem (hK k)))
  have hI (A : Mat) : Integrable (fun k => a k A) ν :=
    (hw.mul (Φ.continuous.comp ((Units.continuous_val.comp hi.inv).matrix_mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨Q, _, hQ⟩ := integral_mem ν V hV hI
  exact ⟨Q, congrFun hQ⟩

private theorem compactPairing_squareZeta (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (i : K →* G) (hi : Continuous i) (hK : ∀ k, i k ∈ Kc) (ν : Measure K) [IsFiniteMeasure ν]
    (w : K → ℂ) (hw : Continuous w) (ds : List RealBlock)
    (f : G → ℂ) (hf : f ∈ principalSeries ℝ n (realPositionCharacter ds))
    (Φ : 𝓢(Mat, ℂ)) (P : Poly) (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) :
    let Z (s : ℂ) (g : G) := realMatrixZetaKernel (r := r)
      (fun x => ∫ k, w k * f (i k * x) ∂ν) Φ s g
    ∃ (β : ℝ) (Q : Polynomial ℂ), ∀ s : ℂ, β < s.re → Integrable (Z s) μ ∧
      (∫ g, Z s g ∂μ) = Q.eval s * torusL (fun j : Fin n => realPositionSign ds j)
        (fun j : Fin n => GramFormula.realPositionExponent ds j) s := by
  intro Z
  obtain ⟨Q, hQ⟩ := exists_squareGaussian_leftAverage i hi hK ν w hw Φ P hΦ
  let Ψ := squarePolynomialSchwartz Q
  have hΨ (A : Mat) : Ψ A = ∫ k, w k * Φ ((i k)⁻¹.val * A) ∂ν := by
    rw [squarePolynomialSchwartz_apply, hQ]
  obtain ⟨N, hN⟩ := exists_uniform_principalSeries_derivative_height r ds
  obtain ⟨C, hC, hCF⟩ := hN f hf []
  have hF (g : G) : ‖f g‖ ≤ C * realMatrixHeight g ^ N := hCF g
  let β : ℝ := (n : ℝ) + 2 * N
  let A (s : ℂ) (g : G) := Φ g.val * D g (s + (r : ℂ) / 2)
  let B (s : ℂ) (p : K × G) := A s p.2 * (w p.1 * f (i p.1 * p.2))
  let T (s : ℂ) (p : K × G) := w p.1 * A s (i p.1⁻¹ * p.2) * f p.2
  have hB (s : ℂ) (hs : β < s.re) : Integrable (B s) (ν.prod μ) := by
    have he : β ≤ (s + (r : ℂ) / 2).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) r]
    let G₀ (g : G) : ℂ := (C * realMatrixHeight g ^ N : ℝ)
    have hG₀ (g : G) : ‖G₀ g‖ = C * realMatrixHeight g ^ N := by
      simp only [G₀, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg hC (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg g) N))]
    have hGm : Measurable G₀ := (Complex.continuous_ofReal.comp
      ((continuous_realMatrixHeight.pow N).const_mul C)).measurable
    have hM := integrable_realMatrixWeightedNorm μ hGm Φ hC (fun g => (hG₀ g).le) he
    have hwI : Integrable (fun k => ‖w k‖) ν :=
      hw.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hAc : Continuous (A s) := by
      have hlog : Continuous (fun g : G => Real.log |g.val.det|) :=
        (continuous_abs.comp Units.continuous_val.matrix_det).log fun g => abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
      exact (Φ.continuous.comp Units.continuous_val).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hlog).const_mul _))
    refine (hwI.mul_prod hM).mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((hAc.comp continuous_snd).mul ((hw.comp continuous_fst).mul
        (hf.1.continuous.comp ((hi.comp continuous_fst).mul continuous_snd)))).aestronglyMeasurable
    · change ‖B s p‖ ≤ ‖w p.1‖ * (‖Φ p.2.val‖ * ‖G₀ p.2‖ *
        |p.2.val.det| ^ (s + (r : ℂ) / 2).re)
      simp only [B, A, norm_mul, norm_realDetPower, hG₀]
      have hF' : ‖f (i p.1 * p.2)‖ ≤ C * realMatrixHeight p.2 ^ N := by
        simpa only [realMatrixHeight_unitary_mul (hK p.1)] using hF (i p.1 * p.2)
      calc
        _ ≤ (‖Φ p.2.val‖ * |p.2.val.det| ^ (s + (r : ℂ) / 2).re) *
            (‖w p.1‖ * (C * realMatrixHeight p.2 ^ N)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hF' (norm_nonneg _)) (by positivity)
        _ = _ := by ring
  have hT (s : ℂ) (hs : β < s.re) : Integrable (T s) (ν.prod μ) :=
    (ComplexJacquet.integrable_compact_average_iff i hi.measurable ν μ w (A s) f).mpr (hB s hs)
  have hTA (s : ℂ) (g : G) : (∫ k, T s (k, g) ∂ν) = realMatrixZetaKernel f Ψ s g := by
    change (∫ k, w k * A s (i k⁻¹ * g) * f g ∂ν) = _
    have hPoint (k : K) : w k * A s (i k⁻¹ * g) * f g =
        (w k * Φ ((i k)⁻¹.val * g.val)) * f g * D g (s + (r : ℂ) / 2) := by
      have hk : |(i k⁻¹).val.det| = 1 := MaximalParabolicIntegration.abs_det_unitary
        ⟨i k⁻¹, hK k⁻¹⟩
      have hd : D (i k⁻¹) (s + (r : ℂ) / 2) = 1 := by
        simp only [ArchimedeanLocal.detPower, realNormalizedAbs, hk, Real.log_one, Complex.ofReal_zero,
          mul_zero, Complex.exp_zero]
      rw [show A s (i k⁻¹ * g) = Φ (i k⁻¹ * g).val * D (i k⁻¹ * g) (s + (r : ℂ) / 2) from rfl,
        RealJacquet.realDetPower_mul, hd, one_mul, map_inv, Units.val_mul]
      ring
    simp only [hPoint, integral_mul_const, realMatrixZetaKernel, hΨ]
  have hBZ (s : ℂ) (g : G) : (∫ k, B s (k, g) ∂ν) = Z s g := by
    simp only [B, integral_const_mul, A, Z, realMatrixZetaKernel]
    ring
  have hEq (s : ℂ) (hs : β < s.re) : (∫ g, Z s g ∂μ) = ∫ g, realMatrixZetaKernel f Ψ s g ∂μ := by
    simp_rw [← hBZ s, ← hTA s]
    rw [← integral_prod_symm _ (hB s hs), ← integral_prod_symm _ (hT s hs),
      integral_prod _ (hB s hs), integral_prod _ (hT s hs)]
    apply integral_congr_ae (ae_of_all _ fun k => ?_)
    rw [← integral_mul_left_eq_self (fun g => T s (k, g)) (i k)]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    change A s g * (w k * f (i k * g)) = w k * A s (i k⁻¹ * (i k * g)) * f (i k * g)
    rw [map_inv, inv_mul_cancel_left]
    ring
  have hZ (s : ℂ) (hs : β < s.re) : Integrable (Z s) μ := by
    rw [← funext (hBZ s)]
    exact (hB s hs).integral_prod_right
  have hKern (s : ℂ) : realMatrixZetaKernel f Ψ s = realMatrixWeightedIntegrand f Ψ (fun x => (x : ℂ) ^ s) :=
    funext (realMatrixZetaKernel_eq f Ψ s)
  obtain ⟨τ, R, hR⟩ := realSquareZetaPolynomial r μ κ (realPositionCharacter ds)
    (fun j => realPositionSign ds j) (fun j => GramFormula.realPositionExponent ds j)
    (fun j x => realPositionCharacter_eq_charFun ds j x) f hf Ψ Q (funext (squarePolynomialSchwartz_apply Q))
    ⟨β, fun s hs => by rw [← hKern s, ← funext (hTA s)]; exact (hT s hs).integral_prod_right⟩
  refine ⟨max β τ, R, fun s hs => ⟨hZ s ((le_max_left _ _).trans_lt hs), ?_⟩⟩
  rw [hEq s ((le_max_left _ _).trans_lt hs), hKern s]
  exact (hR s ((le_max_right _ _).trans_lt hs)).2

end CompactPairing

/-- With a character list in the square principal series and a compactly paired standard
vector, the determinant-twisted square integral is polynomial after normalization by the
pairing of the character twist with that inducing list. -/
def RealCompactSquarePolynomialConclusion : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (i : K →* G), Continuous i → (∀ k, i k ∈ Kc) →
    ∀ (ν : Measure K) [IsFiniteMeasure ν] (w : K → ℂ), Continuous w →
    ∀ (ds : List RealCharacterData), ds.length = n → ∀ (c : RealCharacterData)
      (f : G → ℂ), f ∈ principalSeries ℝ n (realPositionCharacter (ds.map RealBlock.character)) →
    ∀ (Φ : 𝓢(Mat, ℂ)) (P : Poly), (Φ : Mat → ℂ) = squarePolynomialGaussian P →
    let Z (s : ℂ) (g : G) := realAdjacentMatrixWeight c.character.toMonoidHom Φ s g *
      ∫ k, w k * f (i k * g) ∂ν
    ∃ (β : ℝ) (R : Polynomial ℂ), ∀ s : ℂ, β < s.re → Integrable (Z s) μ ∧
      (∫ g, Z s g ∂μ) = R.eval s * ((realPairLFactor [RealBlock.character c]
        (ds.map RealBlock.character)).denominator s)⁻¹

/-- The square polynomial assertion for a compact topological group with its Borel structure. -/
def RealCompactSquarePolynomialStatement [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K] : Prop :=
  RealCompactSquarePolynomialConclusion (r := r) (K := K)

set_option maxHeartbeats 1200000 in
theorem realCompactSquarePolynomial [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K] :
    RealCompactSquarePolynomialStatement (r := r) (K := K) := by
  intro μ _ i hi hK ν _ w hw ds hd c f hf Φ P hΦ Z
  let es := ds.map RealBlock.character
  let fs := twistedPositionList n es c
  let f' (g : G) := realDetCharacter c g * f g
  have hf' : f' ∈ principalSeries ℝ n (realPositionCharacter fs) :=
    realDetCharacter_mul_mem_principalSeries c (realPositionCharacter_twistedPositionList es c) hf
  let w' (k : K) := w k * (realDetCharacter c (i k))⁻¹
  have hw' : Continuous w' := hw.mul (((RealPrincipalSeries.contMDiff_realDetCharacter c).continuous.comp hi).inv₀
    (fun k => realDetCharacter_ne_zero c (i k)))
  let κ : Measure Kc := Measure.haar
  obtain ⟨β, R, hR⟩ := compactPairing_squareZeta μ κ i hi hK ν w' hw' fs f' hf' Φ P hΦ
  have hF : (fun g => ∫ k, w' k * f' (i k * g) ∂ν) =
      fun g => realDetCharacter c g * ∫ k, w k * f (i k * g) ∂ν := by
    funext g
    rw [← integral_const_mul]
    apply integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only [w', f', realDetCharacter_mul]
    field_simp [realDetCharacter_ne_zero c (i k)]
  have hZ (s : ℂ) : realMatrixZetaKernel (r := r) (fun g => ∫ k, w' k * f' (i k * g) ∂ν) Φ s = Z s := by
    rw [hF]
    exact funext (realMatrixZetaKernel_detCharacter c Φ (fun g => ∫ k, w k * f (i k * g) ∂ν) s)
  refine ⟨β, R, fun s hs => ?_⟩
  have h := hR s hs
  simp only [hZ, fs, realPositionSign_twistedPositionList, realPositionExponent_twistedPositionList] at h
  rw [torusL_eq_pair ds hd] at h
  exact h

end Langlands.Global.RankinSelbergGlobal.RealSquarePolynomialGaussian
