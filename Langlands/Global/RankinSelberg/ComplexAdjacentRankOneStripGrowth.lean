import Langlands.Global.RankinSelberg.ComplexAdjacentConvergence
import Langlands.Global.RankinSelberg.ComplexRankZeroStripGrowth
import Langlands.Global.RankinSelberg.ComplexRankZeroWhittaker
import Langlands.Global.RankinSelberg.ComplexSquareZetaStripGrowth

/-! # Strip growth of the complex `GL₂ × GL₁` recursive ordinary tests -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open ArchimedeanLocal
open ComplexGodement (characterWeight normPower)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "G" => Langlands.GeneralLinear 1 ℂ
local notation "G₂" => Langlands.GeneralLinear 2 ℂ
local notation "K" => unitaryCompact ℂ 1
local notation "Mat" => Matrix (Fin 1) (Fin 1) ℂ
local notation "Vec" => Fin 1 → ℂ
local notation "Q" => LeftUnipotentQuotient 0 ℂ

/-- The adjacent unfolded kernel separates when the second coefficient is a character. -/
theorem unfoldedKernel_eq_prod_for_character (d e : ComplexCharacterData)
    (Φ : Mat → ℂ) (φ : Vec → ℂ) (W V : G → ℂ) (C : ℂ)
    (hV : ∀ g, V g = C * (e.character (determinant g) : ℂ)) (s : ℂ) (p : G × Q) :
    unfoldedKernel d 0 s Φ φ W V p =
      ComplexSquareZeta.zetaKernel Φ (ComplexRankZero.characterFunction (d.mul e)) s p.1 *
        complexEqualIntegrand W V φ s p.2 := by
  have hVmul (g h : G) : V (g * h) = V g * (e.character (determinant h) : ℂ) := by
    have hh := ComplexRankZero.characterFunction_mul e g h
    simp only [ComplexRankZero.characterFunction] at hh
    rw [hV (g * h), hh, hV g, mul_assoc]
  simp only [unfoldedKernel, complexEqualIntegrand, ArchimedeanLocal.equalIntegrand,
    ComplexSquareZeta.zetaKernel, zero_add, Nat.cast_one, sub_self, zero_div, add_zero,
    hVmul, ComplexRankZero.characterFunction]
  change Φ p.1.val * ((d.character (determinant p.1) : ℂ) * normPower s (determinant p.1)) * _ =
    Φ p.1.val * ((d.character (determinant p.1) : ℂ) * (e.character (determinant p.1) : ℂ)) *
      normPower s (determinant p.1) * _
  ring

/-- The pair factor of a two-character list with a singleton splits over the two characters. -/
theorem pairFactor_two_one (c d e : ComplexCharacterData) :
    complexPairLFactor [c, d] [e] =
      (complexPairLFactor [c] [e]).mul (complexPairLFactor [d] [e]) := by
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil, List.singleton_append]
  exact complexLFactor_append [c.mul e] [d.mul e]

/-- For an actual `GL₂(ℂ) × GL₁(ℂ)` test with Jacquet's split recursive formula on the padded
subgroup, the ordinary integral has an entire normalization of exponential strip growth. -/
def ComplexAdjacentRankOneStripGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData 0) [SFinite D.measure]
    (μ : Measure G) [SFinite μ] [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (c d e : ComplexCharacterData)
    (W : complexWhittakerModel 0 [c] a) (V : complexWhittakerModel 0 [e] (-a))
    (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)) (Wbig : G₂ → ℂ) (C : ℂ),
    (∀ g : G, Wbig (padGL (Nat.le_succ 1) g) = C *
      characterWeight d (1 / 2) (determinant g) *
        ∫ h : G, Φ (h * g).val * φ (Langlands.RankinSelberg.lastRow h⁻¹) * W.val h⁻¹ *
          characterWeight d 0 (determinant h) ∂μ) →
    ∃ R : OrdinaryIntegralNormalization (complexUnequalIntegral (Nat.lt_succ_self 0) D Wbig V)
      (fun s => ((complexPairLFactor [c, d] [e]).denominator s)⁻¹),
      HasStripExponentialGrowth R.value

theorem complexAdjacentRankOneStripGrowth : ComplexAdjacentRankOneStripGrowthStatement := by
  intro D _ μ _ _ _ κ _ _ a c d e W V Φ φ Wbig C hBig
  obtain ⟨Cw, hW⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel W.2
  obtain ⟨Cv, hV⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel V.2
  obtain ⟨A, hAg⟩ := ComplexRankZero.complexRankZeroStripGrowth D c e W V Cw Cv hW hV φ
  obtain ⟨τa, hτa⟩ := A.eq_on_right
  let f := ComplexRankZero.characterFunction (d.mul e)
  have hmem : f ∈ complexStandardModule (0 + 1) [d.mul e] :=
    (Submodule.mem_inf.mp (ComplexRankZero.characterFunction_mem (d.mul e))).1
  have hf : f ∈ complexStandardModule 1 (List.ofFn fun _ : Fin 1 => d.mul e) := by
    simpa only [List.ofFn_succ, List.ofFn_zero] using hmem
  obtain ⟨τz, Z, hZd, hZg, hZ⟩ := ComplexSquareZeta.complexSquareZetaStripGrowth (r := 0)
    μ κ (fun _ : Fin 1 => d.mul e) Φ f hf
  obtain ⟨τn, hτn⟩ := complexPairLFactor_denominator_ne_zero [d] [e]
  obtain ⟨σ, hσ⟩ := complexAdjacentConvergence (r := 0) D μ d 0 Φ φ a [c] [e] W V
  let R (s : ℂ) := C * (A.value s * Z s)
  have hAd : Differentiable ℂ A.value := fun s => (A.analytic s (mem_univ _)).differentiableAt
  have hRd : Differentiable ℂ R := (hAd.mul hZd).const_mul C
  have hC : HasStripExponentialGrowth (fun _ => C) := by
    intro _ _
    exact ⟨‖C‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩
  have hRg : HasStripExponentialGrowth R := hC.mul (hAg.mul hZg)
  refine ⟨⟨R, fun s _ => hRd.analyticAt s, ⟨max (max σ τa) (max τz τn), fun s hs => ?_⟩⟩, hRg⟩
  have hs₁ := (le_max_left (max σ τa) (max τz τn)).trans_lt hs
  have hs₂ := (le_max_right (max σ τa) (max τz τn)).trans_lt hs
  have hA := hτa s ((le_max_right σ τa).trans_lt hs₁)
  have hZn := hτn s ((le_max_right τz τn).trans_lt hs₂)
  have hZeit := (hZ s ((le_max_left τz τn).trans_lt hs₂)).2
  have hZD : (∫ g : G, ComplexSquareZeta.zetaKernel Φ f s g ∂μ) =
      Z s * ((complexPairLFactor [d] [e]).denominator s)⁻¹ := by
    have hFactor : complexLFactor (List.ofFn fun _ : Fin 1 => d.mul e) = complexPairLFactor [d] [e] := by
      simp [complexPairLFactor, complexPairBlocks, List.ofFn_succ, List.ofFn_zero]
    rw [hFactor] at hZeit
    rw [hZeit, mul_comm ((complexPairLFactor [d] [e]).denominator s), mul_assoc,
      mul_inv_cancel₀ hZn, mul_one]
  have hU := complexAdjacentUnfolding (r := 0) D μ d 0 s Φ φ a W V Wbig C
    (fun u g => complexWhittakerModel_left_equivariant W.2 u.val u.2 g)
    (fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g)
    (fun g => by simpa only [zero_add] using hBig g) (hσ s ((le_max_left σ τa).trans_lt hs₁))
  rw [hU]
  simp_rw [unfoldedKernel_eq_prod_for_character d e Φ φ W V Cv hV s]
  rw [integral_prod_mul, hZD]
  change C * ((_ * complexEqualIntegral D W V φ s)) = R s * _
  rw [hA, pairFactor_two_one, LocalFactor.ReciprocalEntire.denominator_mul, mul_inv]
  dsimp only [R]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
