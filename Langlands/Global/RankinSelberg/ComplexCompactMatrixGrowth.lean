import Langlands.Global.RankinSelberg.ComplexSquareZetaNormalization
import Langlands.Global.RankinSelberg.ComplexTateProductStripGrowth
import Langlands.Representation.GodementJacquet.ComplexPrincipalSeriesCompactEquation

/-! # Normalization and strip growth for the exact compact matrix integrals -/

noncomputable section

open Filter MeasureTheory Topology
open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal
open scoped Matrix.Norms.Elementwise NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open ArchimedeanLocal
open ComplexTateProduct (affineParameter gammaNormalizer normalizedZeta)
open ComplexSquareZeta (denominator_complexLFactor_ofFn)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "ι" => inverseTranspose n ℂ

private theorem exists_entire_normalizedDiagonal (a : ℂˣ) (Φ : 𝓢(I → ℂ, ℂ))
    (ds : I → ComplexCharacterData) :
    ∃ N : ℂ → ℂ, Differentiable ℂ N ∧ HasStripExponentialGrowth N ∧
      ∀ s, (∀ i, 0 < (s + (ds i).exponent).re) →
        N s = (complexLFactor (List.ofFn ds)).denominator s *
          complexDiagonalZeta a Φ (fun i => (ds i).weight) (fun i => s + (ds i).exponent) := by
  obtain ⟨H, hH⟩ := ComplexTateProduct.complexTateProductEntireFamily r
  let t (i : I) := (ds i).exponent
  let m (i : I) := (ds i).weight
  let c : ℂ := complexCoordinateMeasureScale I a
  have hu (s : ℂ) :
      affineParameter t (fun _ => 1) s = fun i => s + t i := by
    funext i
    simp [affineParameter, add_comm]
  refine ⟨fun s => c * H Φ m (affineParameter t (fun _ => 1) s),
    (hH.1 Φ m t (fun _ => 1)).const_mul c,
    HasStripExponentialGrowth.const_mul (ComplexTateProduct.complexTateProductStripGrowth _ H hH Φ m t (fun _ => 1)) c,
    fun s hs => ?_⟩
  change c * H Φ m (affineParameter t (fun _ => 1) s) = _
  rw [hu, hH.2 _ _ _ hs, denominator_complexLFactor_ofFn, complexDiagonalZeta_eq_integral _ _ _ hs,
    complexCoordinateMeasure_eq_smul_volume, integral_smul_nnreal_measure]
  change c * ((∏ i, gammaNormalizer (m i) (s + t i)) *
      ∫ z, complexDiagonalZetaKernel Φ m (fun i => s + t i) z) =
    (∏ i, gammaNormalizer (m i) (s + t i)) *
      ((complexCoordinateMeasureScale I a : ℝ) •
        ∫ z, complexDiagonalZetaKernel Φ m (fun i => s + t i) z)
  rw [Complex.real_smul]
  dsimp only [c]
  ring

private theorem compact_inverseTranspose (μK : Measure Kc) (w : Kc → ℂ) (f : G → ℂ) :
    (fun g : G => ∫ k : Kc, w k * (f ∘ ι) ((unitaryInverseTranspose k).val * g) ∂μK) =
      complexCompactCoefficient μK w f ∘ ι := by
  funext g
  unfold complexCompactCoefficient
  apply integral_congr_ae
  exact .of_forall fun k => by simp only [Function.comp_apply, unitaryInverseTranspose_val,
    map_mul, inverseTranspose_involutive]

/-- The compact coefficient matrix integrals for the positive standard trace character
have entire normalizations of exponential strip growth. -/
def ComplexCompactMatrixGrowthStatement : Prop :=
  ∀ (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK]
    (ds : I → ComplexCharacterData) (χ : ℕ → ℂˣ → ℂ),
    (∀ i : I, ∀ z : ℂˣ, χ i.val z = ((ds i).character z : ℂ)) →
    ∀ (f : G → ℂ) (w : Kc → ℂ) (Φ : 𝓢(M, ℂ)),
    f ∈ principalSeries ℂ n χ → Continuous w →
    let F := complexCompactCoefficient μK w f
    let μ := complexMatrixHaar n (complexMatrixAddMeasure n 1)
    ∃ (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        N s = (complexLFactor (List.ofFn ds)).denominator s *
          ∫ g, complexMatrixZetaIntegrand F Φ s g ∂μ ∧
        Nd s = (complexLFactor ((List.ofFn ds).map ComplexCharacterData.inv)).denominator s *
          ∫ g, complexMatrixZetaIntegrand (F ∘ ι) (complexMatrixFourier 1 Φ) s g ∂μ

set_option maxHeartbeats 1100000 in
theorem complexCompactMatrixGrowth : ComplexCompactMatrixGrowthStatement (r := r) := by
  intro μK _ _ ds χ hχ f w Φ hf hw
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact n
  let : SecondCountableTopology G :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
  let : SecondCountableTopology Kc := IsInducing.subtypeVal.secondCountableTopology
  have hwI : Integrable w μK :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P := complexMatrixInverseLeftAverage μK w hwI Φ
  obtain ⟨c, _, hDiag⟩ := exists_complexMatrixZeta_diagonalTests (r := r) 1 μK
  obtain ⟨A, Ad, _, hA, hAd⟩ := hDiag χ f hf P
  let ds' (j : I) := (ds j).inv
  obtain ⟨N, hN, hNg, hNr⟩ := exists_entire_normalizedDiagonal 1 A ds
  obtain ⟨Nd, hNd, hNdg, hNdr⟩ := exists_entire_normalizedDiagonal 1 Ad ds'
  obtain ⟨C, M₀, hC, hGrowth⟩ := exists_complexPrincipalSeries_height_bound ds χ hχ f hf
  obtain ⟨B, hB⟩ := Finite.exists_le (fun j : I => |(ds j).exponent.re|)
  have hP : (fun X : M => ∫ k : Kc, w k * Φ ((k.val⁻¹).val * X) ∂μK) = (P : M → ℂ) :=
    funext fun X => (complexMatrixInverseLeftAverage_apply μK w hwI Φ X).symm
  obtain ⟨Φd, hΦd⟩ := exists_schwartz_complexMatrixFourier 1 Φ
  change (Φd : M → ℂ) = complexMatrixFourier 1 Φ at hΦd
  have hPd : (fun X : M => ∫ k : Kc, w k * Φd (((unitaryInverseTranspose k).val⁻¹).val * X) ∂μK) =
      complexMatrixFourier 1 P := by
    funext X
    simp only [hΦd, unitaryInverseTranspose_val]
    exact (complexMatrixFourier_inverseLeftAverage 1 μK w hwI hw Φ X).symm
  have hfc := continuous_complexPrincipalSeries hf
  have hfd : Continuous (f ∘ ι) := hfc.comp (continuous_inverseTranspose n ℂ)
  have hBoundD (g : G) : ‖(f ∘ ι) g‖ ≤ C * complexMatrixHeight g ^ M₀ := by
    simpa only [Function.comp_apply, complexMatrixHeight_inverseTranspose] using hGrowth (ι g)
  have hχP (i : I) (z : ℂˣ) : χ i.val z =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (ds i).weight * (‖(z : ℂ)‖ : ℂ) ^ (2 * (ds i).exponent) :=
    (hχ i z).trans ((ds i).character_eq z)
  have hχD (i : I) (z : ℂˣ) : χ i.val z⁻¹ =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (ds' i).weight * (‖(z : ℂ)‖ : ℂ) ^ (2 * (ds' i).exponent) :=
    (hχ i z⁻¹).trans (complexCharacterData_inv_polar (ds i) z)
  refine ⟨fun s => (c : ℂ) * N s, fun s => (c : ℂ) * Nd s, hN.const_mul _, hNd.const_mul _,
    HasStripExponentialGrowth.const_mul hNg _, HasStripExponentialGrowth.const_mul hNdg _, max B ((n : ℝ) + M₀), ?_⟩
  intro s hs
  have hsB := (le_max_left B _).trans_lt hs
  have hsM := (le_max_right B _).trans_lt hs
  have hp (i : I) : 0 < (s + (ds i).exponent).re := by
    rw [Complex.add_re]
    linarith [(neg_le_abs (ds i).exponent.re).trans (hB i)]
  have hd (i : I) : 0 < (s + (ds' i).exponent).re := by
    simp only [ds', ComplexCharacterData.inv_exponent, Complex.add_re, Complex.neg_re]
    linarith [(le_abs_self (ds i).exponent.re).trans (hB i)]
  have hS : (n : ℝ) + M₀ ≤ (s + (r : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hpr := (integral_complexCompactCoefficient_changeTest 1 μK w hwI hw id continuous_id
    hfc Φ hC hGrowth hS).2
  have hdr := (integral_complexCompactCoefficient_changeTest 1 μK w hwI hw
    unitaryInverseTranspose unitaryInverseTranspose.continuous hfd Φd hC hBoundD hS).2
  dsimp only [id] at hpr
  rw [hP] at hpr
  let μ := complexMatrixHaar n (complexMatrixAddMeasure n 1)
  change (∫ g, complexMatrixZetaIntegrand (complexCompactCoefficient μK w f) Φ s g ∂μ) = _ at hpr
  rw [compact_inverseTranspose, hPd, hΦd] at hdr
  have hPint : Integrable (complexMatrixZetaIntegrand f P s) μ :=
    integrable_complexMatrixZetaKernel (complexMatrixAddMeasure n 1) hfc.measurable P hC hGrowth hS
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexMatrixFourier 1 P
  change (Ψ : M → ℂ) = complexMatrixFourier 1 P at hΨ
  have hDint : Integrable (complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier 1 P) s) μ := by
    rw [← hΨ]
    exact integrable_complexMatrixZetaKernel (complexMatrixAddMeasure n 1)
      hfd.measurable Ψ hC hBoundD hS
  have hlist : List.ofFn ds' = (List.ofFn ds).map ComplexCharacterData.inv := by
    rw [List.map_ofFn]
    rfl
  constructor
  · change (c : ℂ) * N s = _
    rw [hpr, hA s hPint, integral_complexDiagonalZetaWeight 1 χ
      (fun j => (ds j).weight) (fun j => (ds j).exponent) hχP A s hp, hNr s hp]
    ring
  · change (c : ℂ) * Nd s = _
    rw [hdr, hAd s hDint, integral_complexDiagonalZetaWeight 1 (fun i z => χ i z⁻¹)
      (fun j => (ds' j).weight) (fun j => (ds' j).exponent) hχD Ad s hd, hNdr s hd, hlist]
    ring

end Langlands.GodementJacquet
