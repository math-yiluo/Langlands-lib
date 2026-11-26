import Langlands.Global.RankinSelberg.ComplexAdjacentSquareTrace
import Langlands.Global.RankinSelberg.ComplexAdjacentGodementPolynomial
import Langlands.Global.RankinSelberg.ComplexLocalEqualNormalizedFactors
import Langlands.Global.RankinSelberg.ComplexLocalEqualProductConvergence

/-! # Equal-rank normalized square convolution in the adjoining chamber -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ComplexGodement (shiftedCharacter shiftedCharacter_exponent)
open ComplexAdjacentUnfolding (complexUnequalOrdinaryKernel whittakerVector whittakerVector_val)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable {r t : ℕ}
local notation "GLc" => fun n : ℕ => Langlands.GeneralLinear n ℂ

/-- With the smaller coefficient fixed, the ordinary unequal-rank normalized integral is linear
in the larger inducing vector. -/
theorem exists_complexUnequalNormalizationLinear (h : t < r) (D : ComplexQuotientMeasureData t) (a : ℂˣ)
    (ds es : List ComplexCharacterData) (hd : ds.length = r + 1) (he : es.length = t + 1)
    (U : complexWhittakerModel t es (-a))
    (B : complexStandardKFinite (r + 1) ds →ₗ[ℂ] (GLc (r + 1) → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) :
    ∃ A : complexStandardKFinite (r + 1) ds →ₗ[ℂ] (ℂ → ℂ), ∀ v,
      ∃ N : OrdinaryIntegralNormalization (complexUnequalIntegral h D (B v) U.val)
        (fun s => ((complexPairLFactor ds es).denominator s)⁻¹), A v = N.value := by
  classical
  let K := (complexUnequalOrdinaryKernel h U.val).comp B
  let L (s : ℂ) := ((complexPairLFactor ds es).denominator s)⁻¹
  have hI (v : complexStandardKFinite (r + 1) ds) :
      ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (K v s) D.measure :=
    complexLocalOrdinaryConvergence h ds es a D (whittakerVector hB v) U
  let N (v : complexStandardKFinite (r + 1) ds) :
      OrdinaryIntegralNormalization (fun s => ∫ q, K v s q ∂D.measure) L :=
    Classical.choice (complexOrdinaryNormalizedContinuation.1 r t h ds es hd he a D (whittakerVector hB v, U))
  obtain ⟨b, hb⟩ := complexPairLFactor_denominator_ne_zero ds es
  obtain ⟨A, hA⟩ := ordinaryNormalizationLinear D.measure K L ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩ hI N
  exact ⟨A, fun v => ⟨N v, hA v⟩⟩

local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 1 + 1 : ℕ)
local notation "G" => GLc n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "gap" => Nat.lt_succ_self r
local notation "pad" => padGL (R := ℂ) (Nat.le_succ m)
local notation "KF[" es "]" => complexStandardKFinite n es

private theorem shiftedJacquetMatrixIntegrand (d : ComplexCharacterData) (b : G → ℂ)
    (Φ : Mat → ℂ) (z s : ℂ) (g : G) :
    complexJacquetMatrixIntegrand (shiftedCharacter d z) b Φ s g =
      complexJacquetMatrixIntegrand d b Φ (s + z) g := by
  rw [complexJacquetMatrixIntegrand, complexJacquetMatrixIntegrand, shiftedCharacter_det_apply]
  simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]
  ring

/-- In the positive adjoining and spectral chambers, the normalized double integral is the
lower adjacent normalized functional applied to the square convolution at the shifted parameter. -/
def ComplexEqualSquareTraceChamberStatement : Prop :=
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (e : Fin n → ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (B : KF[List.ofFn e] →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-a) B →
    ∀ (Φ : 𝓢(Mat, ℂ)) (f : KF[List.ofFn e]) (F : ℂ → KF[List.ofFn e]),
      HasSquareConvolutionTrace D.groupHaar d e B Φ f F →
    ∀ A : KF[List.ofFn e] →ₗ[ℂ] (ℂ → ℂ),
      (∀ v, ∃ N : OrdinaryIntegralNormalization (complexUnequalIntegral gap D₁ (B v) U.val)
        (fun s => ((complexPairLFactor (List.ofFn e) ds).denominator s)⁻¹), A v = N.value) →
    ∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
      equalDoubleDenominator d ds (List.ofFn e) z s *
        complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d z).character Φ U.val (B f) s =
        A (F (s + z)) s

set_option maxHeartbeats 1200000 in
theorem complexEqualSquareTraceChamber : ComplexEqualSquareTraceChamberStatement (r := r) := by
  intro a D D₁ d ds e U B hB Φ f F hF A hA
  let es := List.ofFn e
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite μ := complexLocalGroupHaarSigmaFinite D
  let : SigmaFinite D₁.measure := complexLocalQuotientSigmaFinite D₁
  let V := whittakerVector hB f
  obtain ⟨T, σ, hConv⟩ := complexLocalEqualProductConvergence D₁ μ a ds es U V
  obtain ⟨bF, hbF⟩ := hF.2
  obtain ⟨l, p, v, hpoly⟩ := hF.1
  choose N hN using fun j => hA (v j)
  choose bj hbj using fun j => (N j).eq_on_right
  let U' : complexWhittakerModel r ds (-(-a)) := ⟨U, by simpa only [neg_neg] using U.2⟩
  choose cj hcj using fun j => complexLocalOrdinaryConvergence gap es ds (-a) D₁ (whittakerVector hB (v j)) U'
  obtain ⟨b₀, hb₀⟩ := (finite_range fun j => max (bj j) (cj j)).bddAbove
  obtain ⟨bL, hbL⟩ := complexPairLFactor_denominator_ne_zero [d] es
  obtain ⟨bJ, hbJ⟩ := complexPairLFactor_denominator_ne_zero es ds
  let τ := max (T - d.exponent.re) 0
  let β := max (max σ b₀) (max (max bF bL) bJ)
  let L (s : ℂ) := (complexPairLFactor [d] es).denominator s
  let M (s : ℂ) := (complexPairLFactor es ds).denominator s
  let K := (complexUnequalOrdinaryKernel gap U.val).comp B
  refine ⟨τ, β, fun z s hz hs => ?_⟩
  have hz₀ : 0 < z.re := (le_max_right (T - d.exponent.re) 0).trans_lt hz
  have hd : T ≤ (shiftedCharacter d z).exponent.re := by
    rw [shiftedCharacter_exponent, Complex.add_re]
    linarith [(le_max_left (T - d.exponent.re) 0).trans_lt hz]
  have h₁ := (le_max_left (max σ b₀) (max (max bF bL) bJ)).trans_lt hs
  have h₂ := (le_max_right (max σ b₀) (max (max bF bL) bJ)).trans_lt hs
  have hsF : bF < (s + z).re := by
    rw [Complex.add_re]
    linarith [(le_max_left bF bL).trans_lt ((le_max_left (max bF bL) bJ).trans_lt h₂)]
  have hsL : bL < (s + z).re := by
    rw [Complex.add_re]
    linarith [(le_max_right bF bL).trans_lt ((le_max_left (max bF bL) bJ).trans_lt h₂)]
  have hL : L (s + z) ≠ 0 := hbL _ hsL
  have hM : M s ≠ 0 := hbJ s ((le_max_right (max bF bL) bJ).trans_lt h₂)
  have hI := hConv (shiftedCharacter d z) hd Φ s ((le_max_left σ b₀).trans_lt h₁)
  let J := complexEqualUnfoldedKernel (shiftedCharacter d z) Φ U.val (B f) s
  have hRaw : complexEqualUnfoldedIntegral μ D₁ (shiftedCharacter d z).character Φ U.val (B f) s =
      ∫ q, ∫ g, J (q, g) ∂μ ∂D₁.measure := by
    calc
      _ = ∫ g, ∫ q, J (q, g) ∂D₁.measure ∂μ := by
        apply integral_congr_ae (ae_of_all _ fun g => ?_)
        rw [← integral_const_mul]
        rfl
      _ = ∫ p, J p ∂D₁.measure.prod μ := (integral_prod_symm J hI).symm
      _ = _ := integral_prod J hI
  have hEach (q : Q) : (∫ g, J (q, g) ∂μ) = (L (s + z))⁻¹ * K (F (s + z)) s q := by
    let E := U.val q.out * ArchimedeanLocal.detPower complexNormalizedAbs q.out (s - 1 / 2)
    let C (g : G) := complexJacquetMatrixIntegrand d (fun g => B f (pad q.out * g)) Φ (s + z) g
    have hJ (g : G) : J (q, g) = E * C g := by
      dsimp only [J, complexEqualUnfoldedKernel, complexEqualUnfoldedInner, E, C]
      rw [← shiftedJacquetMatrixIntegrand]
      simp only [complexJacquetMatrixIntegrand]
      ring
    have hC : (∫ g, C g ∂μ) = (L (s + z))⁻¹ * B (F (s + z)) (pad q.out) := by
      rw [hbF _ hsF]
      change _ = (L (s + z))⁻¹ * (L (s + z) * ∫ g, C g ∂μ)
      rw [← mul_assoc, inv_mul_cancel₀ hL, one_mul]
    simp_rw [hJ]
    rw [integral_const_mul, hC]
    change E * _ = _ * (B (F (s + z)) (pad q.out) * U.val q.out *
      ArchimedeanLocal.detPower complexNormalizedAbs q.out (s - ((r + 1 - r : ℕ) : ℂ) / 2))
    rw [show r + 1 - r = 1 by omega, Nat.cast_one]
    dsimp only [E]
    ring
  have hNₛ : (∫ q, K (F (s + z)) s q ∂D₁.measure) = A (F (s + z)) s * (M s)⁻¹ := by
    have hBounds (j : Fin l) : max (bj j) (cj j) < s.re :=
      (hb₀ (mem_range_self j)).trans_lt ((le_max_right σ b₀).trans_lt h₁)
    simp only [hpoly (s + z), map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum]
    · simp only [integral_const_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hNj : (∫ q, K (v j) s q ∂D₁.measure) = (N j).value s * (M s)⁻¹ :=
        hbj j s ((le_max_left _ _).trans_lt (hBounds j))
      rw [hNj, hN j, mul_assoc]
    · exact fun j _ => ((hcj j s ((le_max_right _ _).trans_lt (hBounds j))) : Integrable (K (v j) s) D₁.measure).const_mul _
  change (M s * L (s + z)) * _ = _
  rw [hRaw]
  simp_rw [hEach, integral_const_mul]
  rw [hNₛ]
  field_simp [hL, hM]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
