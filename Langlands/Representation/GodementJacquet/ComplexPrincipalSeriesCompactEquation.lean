import Langlands.Representation.GodementJacquet.ComplexMatrixCoefficientIntegral
import Langlands.LocalFactor.Archimedean.ComplexTateProof

/-! # The complex matrix equation for compact principal series pairings -/

noncomputable section

open MeasureTheory Topology
open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal (complexMatrixHeight)

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "ι" => inverseTranspose n ℂ

local instance compactEquationGLMeasurable (m : ℕ) : MeasurableSpace (GeneralLinear m ℂ) := borel _
local instance compactEquationGLBorel (m : ℕ) : BorelSpace (GeneralLinear m ℂ) := ⟨rfl⟩
local instance compactEquationGLSecondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).isInducing.secondCountableTopology
local instance compactEquationUnitarySecondCountable (m : ℕ) :
    SecondCountableTopology (unitaryCompact ℂ m) := IsInducing.subtypeVal.secondCountableTopology

/-- The matrix coefficient obtained from a compact pairing. -/
def complexCompactCoefficient (μK : Measure Kc) (κ : Kc → ℂ) (f : G → ℂ) (g : G) : ℂ :=
  ∫ k, κ k * f (k.val * g) ∂μK

private theorem complexCompactCoefficient_inverseTranspose (μK : Measure Kc)
    (κ : Kc → ℂ) (f : G → ℂ) :
    (fun g : G => ∫ k, κ k * (f ∘ ι) ((unitaryInverseTranspose k).val * g) ∂μK) =
      complexCompactCoefficient μK κ f ∘ ι := by
  funext g
  unfold complexCompactCoefficient
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => by
    simp only [Function.comp_apply, unitaryInverseTranspose_val, map_mul, inverseTranspose_involutive]

/-- A smooth complex principal series vector paired against any continuous
compact test gives a matrix coefficient satisfying the matrix equation. -/
theorem complexCompactCoefficient_matrixZetaFunctionalEquation
    (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK]
    (d : I → ComplexCharacterData) (χ : ℕ → ℂˣ → ℂ)
    (hχ : ∀ i : I, ∀ z : ℂˣ, χ i.val z = ((d i).character z : ℂ))
    (f : G → ℂ) (hf : f ∈ principalSeries ℂ n χ) (κ : Kc → ℂ) (hκc : Continuous κ)
    (Φ : SchwartzMap M ℂ) :
    HasComplexMatrixZetaFunctionalEquation d (complexCompactCoefficient μK κ f) Φ := by
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact n
  have hκ : Integrable κ μK := hκc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, N, hC, hGrowth⟩ := exists_complexPrincipalSeries_height_bound d χ hχ f hf
  let P := complexMatrixInverseLeftAverage μK κ hκ Φ
  obtain ⟨Z, Zdual, hZ, hZdual, ⟨σ, hσ⟩, hFE⟩ :=
    exists_complexPrincipalSeries_matrixZetaFunctionalEquation
      ComplexTate.complexArchimedeanTateStatement μK d χ hχ f hf P hC hGrowth
  refine ⟨Z, Zdual, hZ, hZdual, ⟨max σ ((n : ℝ) + N), ?_⟩, hFE⟩
  intro s hs
  obtain ⟨_, _, hprimal, hdual⟩ := hσ s (lt_of_le_of_lt (le_max_left σ _) hs)
  have hsr : (n : ℝ) + N ≤ (s + (r : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith [lt_of_le_of_lt (le_max_right σ _) hs, show (0 : ℝ) ≤ r by positivity]
  have hfc := continuous_complexPrincipalSeries hf
  have hp := integral_complexCompactCoefficient_changeTest 1 μK κ hκ hκc id continuous_id hfc Φ hC hGrowth hsr
  have hp' : (fun X : M => ∫ k : Kc, κ k * Φ ((k.val⁻¹).val * X) ∂μK) = (P : M → ℂ) :=
    funext fun X => (complexMatrixInverseLeftAverage_apply μK κ hκ Φ X).symm
  dsimp only [id] at hp
  rw [hp'] at hp
  obtain ⟨Φf, hΦf⟩ := exists_schwartz_complexMatrixFourier 1 Φ
  have hΦf' : (Φf : M → ℂ) = complexMatrixFourier 1 Φ := hΦf
  have hfdual : Continuous (f ∘ ι) := hfc.comp (continuous_inverseTranspose n ℂ)
  have hboundDual (g : G) : ‖(f ∘ ι) g‖ ≤ C * complexMatrixHeight g ^ N := by
    simpa only [Function.comp_apply, complexMatrixHeight_inverseTranspose] using hGrowth (ι g)
  have hd := integral_complexCompactCoefficient_changeTest 1 μK κ hκ hκc
    unitaryInverseTranspose unitaryInverseTranspose.continuous hfdual Φf hC hboundDual hsr
  have hd' : (fun X : M => ∫ k : Kc, κ k * Φf (((unitaryInverseTranspose k).val⁻¹).val * X) ∂μK) =
      complexMatrixFourier 1 P := by
    funext X
    simp only [hΦf', unitaryInverseTranspose_val]
    exact (complexMatrixFourier_inverseLeftAverage 1 μK κ hκ hκc Φ X).symm
  dsimp only at hd
  rw [complexCompactCoefficient_inverseTranspose μK κ f, hd', hΦf'] at hd
  exact ⟨hp.1, hd.1, hprimal.trans hp.2.symm, hdual.trans hd.2.symm⟩

/-- The matrix functional equation for continuous compact pairings of complex
principal series vectors, at the standard trace character. -/
def ComplexPrincipalSeriesCompactEquationStatement : Prop :=
  ∀ (r : ℕ) (μK : Measure (unitaryCompact ℂ (r + 1))) [μK.IsHaarMeasure] [SFinite μK]
    (d : Fin (r + 1) → ComplexCharacterData) (χ : ℕ → ℂˣ → ℂ),
    (∀ i : Fin (r + 1), ∀ z : ℂˣ, χ i.val z = ((d i).character z : ℂ)) →
    ∀ f : GeneralLinear (r + 1) ℂ → ℂ, f ∈ principalSeries ℂ (r + 1) χ →
    ∀ κ : unitaryCompact ℂ (r + 1) → ℂ, Continuous κ →
    ∀ Φ : SchwartzMap (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) ℂ,
      HasComplexMatrixZetaFunctionalEquation d (complexCompactCoefficient μK κ f) Φ

theorem complexPrincipalSeriesCompactEquation : ComplexPrincipalSeriesCompactEquationStatement := by
  intro r μK _ _ d χ hχ f hf κ hκ Φ
  exact complexCompactCoefficient_matrixZetaFunctionalEquation μK d χ hχ f hf κ hκ Φ

end Langlands.GodementJacquet
