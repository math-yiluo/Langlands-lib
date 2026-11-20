import Langlands.Representation.GodementJacquet.ComplexMatrixAveragedZeta
import Langlands.Representation.GodementJacquet.ComplexMatrixConvergence
import Langlands.Representation.GodementJacquet.ComplexDiagonalWeightTransport
import Langlands.Representation.GodementJacquet.ComplexDiagonalTateEquation

/-! # The matrix functional equation for a complex principal series vector -/

noncomputable section

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "ι" => inverseTranspose n ℂ

local instance matrixEquationGLMeasurable (m : ℕ) : MeasurableSpace (GeneralLinear m ℂ) := borel _
local instance matrixEquationGLBorel (m : ℕ) : BorelSpace (GeneralLinear m ℂ) := ⟨rfl⟩
local instance matrixEquationGLSecondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).isInducing.secondCountableTopology

/-- The height bound is unchanged by inverse transpose. -/
theorem complexMatrixHeight_inverseTranspose (g : G) :
    complexMatrixHeight (ι g) = complexMatrixHeight g := by
  simp only [complexMatrixHeight, inverseTranspose_coe, ← map_inv, inv_inv, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => add_comm _ _

/-- Absolute convergence, meromorphic continuation and the normalized
matrix functional equation at the basic trace character. -/
def HasComplexMatrixZetaFunctionalEquation (d : I → ComplexCharacterData)
    (f : G → ℂ) (Φ : SchwartzMap M ℂ) : Prop :=
    let μ := complexMatrixHaar n (complexMatrixAddMeasure n 1)
    let m (i : I) := (d i).weight
    let t (i : I) := (d i).exponent
    ∃ (Z Zdual : ℂ → ℂ), Meromorphic Z ∧ Meromorphic Zdual ∧
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexMatrixZetaIntegrand f Φ s) μ ∧
        Integrable (complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier 1 Φ) s) μ ∧
        Z s = (∫ g, complexMatrixZetaIntegrand f Φ s g ∂μ) ∧
        Zdual s = (∫ g, complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier 1 Φ) s g ∂μ)) ∧
      ∀ s₀ : ℂ,
        (fun s : ℂ => Zdual (1 - s) / complexDiagonalGamma (-m) (fun i => 1 - (s + t i)))
          =ᶠ[𝓝[≠] s₀]
        (fun s : ℂ => complexDiagonalStandardEpsilon m * (Z s / complexDiagonalGamma m (fun i => s + t i)))

/-- The normalized complex matrix functional equation for a principal series
vector evaluated at the identity. The two continuations agree with the
absolutely convergent matrix integrals in a common right half-plane. -/
theorem exists_complexPrincipalSeries_matrixZetaFunctionalEquation
    (hTate : ComplexArchimedeanTateStatement)
    (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK]
    (d : I → ComplexCharacterData) (χ : ℕ → ℂˣ → ℂ)
    (hχ : ∀ i : I, ∀ z : ℂˣ, χ i.val z = ((d i).character z : ℂ))
    (f : G → ℂ) (hf : f ∈ principalSeries ℂ n χ) (Φ : SchwartzMap M ℂ)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hGrowth : ∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ N) :
    HasComplexMatrixZetaFunctionalEquation d f Φ := by
  dsimp only [HasComplexMatrixZetaFunctionalEquation]
  let μ := complexMatrixHaar n (complexMatrixAddMeasure n 1)
  let m (i : I) := (d i).weight
  let t (i : I) := (d i).exponent
  have h₁ (i : I) (z : ℂˣ) :
      χ i.val z = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m i * (‖(z : ℂ)‖ : ℂ) ^ (2 * t i) :=
    (hχ i z).trans ((d i).character_eq z)
  have h₂ (i : I) (z : ℂˣ) :
      χ i.val z⁻¹ = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (-m i) * (‖(z : ℂ)‖ : ℂ) ^ (2 * -t i) :=
    (hχ i z⁻¹).trans (complexCharacterData_inv_polar (d i) z)
  obtain ⟨c, _, hdiag⟩ := exists_complexMatrixZeta_diagonalTests (r := r) 1 μK
  obtain ⟨A, Af, hAf, hp, hd⟩ := hdiag χ f hf Φ
  let Z (s : ℂ) := ((c : ℝ) : ℂ) * complexDiagonalZeta 1 A m (fun i => s + t i)
  let Zdual (s : ℂ) := ((c : ℝ) : ℂ) * complexDiagonalZeta 1 Af (-m) (fun i => s - t i)
  refine ⟨Z, Zdual, ?_, ?_, ?_, ?_⟩
  · intro s
    apply (MeromorphicAt.const _ s).mul
    simpa only [Complex.ofReal_one, one_mul] using
      meromorphic_complexDiagonalZeta_affine 1 A m (fun _ => 1) t s
  · intro s
    apply (MeromorphicAt.const _ s).mul
    simpa only [Complex.ofReal_one, one_mul, sub_eq_add_neg] using
      meromorphic_complexDiagonalZeta_affine 1 Af (-m) (fun _ => 1) (fun i => -(t i)) s
  · have hfc := continuous_complexPrincipalSeries hf
    have hfdual : Continuous (f ∘ ι) := hfc.comp (continuous_inverseTranspose n ℂ)
    have hboundDual (g : G) : ‖(f ∘ ι) g‖ ≤ C * complexMatrixHeight g ^ N := by
      simpa only [Function.comp_apply, complexMatrixHeight_inverseTranspose] using hGrowth (ι g)
    obtain ⟨Φf, hΦf⟩ := exists_schwartz_complexMatrixFourier 1 Φ
    have hΦf' : (Φf : M → ℂ) = complexMatrixFourier 1 Φ := hΦf
    obtain ⟨B, hB⟩ := Finite.exists_le (fun i => |(t i).re|)
    refine ⟨max B ((n : ℝ) + N), fun s hs => ?_⟩
    have hsp (i : I) : 0 < (s + t i).re := by
      rw [Complex.add_re]
      linarith [lt_of_le_of_lt (le_max_left B _) hs, (neg_le_abs (t i).re).trans (hB i)]
    have hsd (i : I) : 0 < (s + (-t i)).re := by
      rw [Complex.add_re, Complex.neg_re]
      linarith [lt_of_le_of_lt (le_max_left B _) hs, (le_abs_self (t i).re).trans (hB i)]
    have hsr : (n : ℝ) + N ≤ (s + (r : ℂ) / 2).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
      linarith [lt_of_le_of_lt (le_max_right B _) hs, show (0 : ℝ) ≤ r by positivity]
    have hip : Integrable (complexMatrixZetaIntegrand f Φ s) μ :=
      integrable_complexMatrixZetaKernel (complexMatrixAddMeasure n 1) hfc.measurable Φ hC hGrowth hsr
    have hid : Integrable (complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier 1 Φ) s) μ := by
      rw [← hΦf']
      exact integrable_complexMatrixZetaKernel (complexMatrixAddMeasure n 1)
        hfdual.measurable Φf hC hboundDual hsr
    refine ⟨hip, hid, ?_, ?_⟩
    · rw [hp s hip, integral_complexDiagonalZetaWeight 1 χ m t h₁ A s hsp]
    · rw [hd s hid, integral_complexDiagonalZetaWeight 1 (fun i z => χ i z⁻¹)
        (-m) (fun i => -(t i)) h₂ Af s hsd]
      rfl
  · intro s₀
    filter_upwards [complexDiagonalTateEquation hTate A Af hAf m t s₀] with s hs
    have he : (fun i => (1 - s) - t i) = fun i => 1 - (s + t i) := by
      funext i
      ring
    change Zdual (1 - s) / complexDiagonalGamma (-m) (fun i => 1 - (s + t i)) =
      complexDiagonalStandardEpsilon m * (Z s / complexDiagonalGamma m (fun i => s + t i))
    simp only [Z, Zdual, he, mul_div_assoc]
    rw [hs]
    ring

end Langlands.GodementJacquet
