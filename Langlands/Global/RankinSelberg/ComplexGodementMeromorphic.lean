import Langlands.Global.RankinSelberg.ComplexGodementProductTate
import Langlands.Global.RankinSelberg.ComplexGodementStandardGrowth
import Langlands.Global.RankinSelberg.ComplexTateProductContinuation
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction

/-! # The Gamma factor and meromorphic continuation of complex Godement sections -/

noncomputable section

open MeasureTheory Matrix
open scoped SchwartzMap Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open ComplexTateProduct (affineParameter normalizedZeta gammaNormalizer complexTateProductContinuation)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance meromorphicGodementGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _

variable {n : ℕ}

/-- The standard factor for the Godement section, as a function of the spectral shift
of its distinguished character. -/
def godementLFactor (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData) : ReciprocalEntire :=
  (complexPairLFactor [d] ((List.ofFn es).map ComplexCharacterData.inv)).shift 1

private def offset (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData) (j : Fin n) : ℂ :=
  d.exponent - (es j).exponent + 1

private def angular (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData) (j : Fin n) : ℤ :=
  d.weight - (es j).weight

theorem godementLFactor_denominator (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData)
    (s : ℂ) : (godementLFactor d es).denominator s =
      ∏ j, gammaNormalizer (angular d es j) (affineParameter (offset d es) 1 s j) := by
  change (complexLFactor (complexPairBlocks [d] ((List.ofFn es).map ComplexCharacterData.inv))).denominator
    (s + 1) = _
  rw [denominator_complexLFactor]
  simp only [complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  simp only [ComplexCharacterData.lFactor, complexTateL, ReciprocalEntire.shift, gammaComplex,
    gammaNormalizer, affineParameter, offset, angular, Pi.one_apply, Complex.ofReal_one, one_mul,
    Function.comp_apply, ComplexCharacterData.mul, ComplexCharacterData.inv_exponent,
    ComplexCharacterData.inv_weight, sub_eq_add_neg]
  congr 2
  ring

private theorem godementLFactor_denominator_ne_zero (d : ComplexCharacterData)
    (es : Fin n → ComplexCharacterData) (s : ℂ)
    (hs : ∀ j, 0 < (affineParameter (offset d es) 1 s j).re) :
    (godementLFactor d es).denominator s ≠ 0 := by
  rw [godementLFactor_denominator]
  refine Finset.prod_ne_zero_iff.mpr fun j _ h => ?_
  let z := affineParameter (offset d es) 1 s j + ((angular d es j).natAbs : ℂ) / 2
  have hz : 0 < z.re := by
    dsimp only [z]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have := hs j
    positivity
  have hP : gammaComplex.IsPole z := h
  obtain ⟨k, hk⟩ := (gammaComplex_isPole z).mp hP
  rw [hk, Complex.neg_re, Complex.natCast_re] at hz
  linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem differentiable_characterWeight_exponent (d : ComplexCharacterData) (u : ℂ) (z : ℂˣ) :
    Differentiable ℂ (fun s => characterWeight (characterOfParams d.weight (d.exponent + s)) u z) := by
  have hne : (‖(z : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero)
  have h (s : ℂ) : characterWeight (characterOfParams d.weight (d.exponent + s)) u z =
      ((((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ d.weight) *
        Complex.exp (Complex.log (‖(z : ℂ)‖ : ℂ) * (2 * (d.exponent + s)))) * normPower u z := by
    change ((characterOfParams d.weight (d.exponent + s)).character z : ℂ) * normPower u z = _
    rw [(characterOfParams d.weight (d.exponent + s)).character_eq, characterOfParams_weight,
      characterOfParams_exponent, Complex.cpow_def_of_ne_zero hne]
  simp only [h]
  fun_prop

/-- At each larger group element, the Godement section has a meromorphic continuation in the
added exponent, expressed as an entire numerator times its standard product of Tate factors. -/
def ComplexGodementMeromorphicStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (κ : Measure (unitaryCompact ℂ n)), κ.IsHaarMeasure →
    ∀ (es : Fin n → ComplexCharacterData), ∃ B : ℝ,
      ∀ (d : ComplexCharacterData) (Φ : 𝓢(Matrix (Fin n) (Fin (n + 1)) ℂ, ℂ))
        (f : Langlands.GeneralLinear n ℂ → ℂ),
        f ∈ complexStandardModule n (List.ofFn es) → ∀ g : Langlands.GeneralLinear (n + 1) ℂ,
          ∃ N Z : ℂ → ℂ, Differentiable ℂ N ∧ Meromorphic Z ∧
            (∀ s, Z s = N s / (godementLFactor d es).denominator s) ∧
            ∀ s : ℂ, B < d.exponent.re + s.re →
              let dₛ := characterOfParams d.weight (d.exponent + s)
              Integrable (godementSectionIntegrand dₛ Φ f g) (complexGeneralLinearHaar n) ∧
              (godementLFactor d es).denominator s ≠ 0 ∧
              Z s = godementSection (complexGeneralLinearHaar n) dₛ Φ f g

theorem complexGodementMeromorphic : ComplexGodementMeromorphicStatement := by
  intro n hn κ hκ es
  let μ := complexGeneralLinearHaar n
  obtain ⟨c, _, hTate⟩ := complexGodementProductTate μ κ inferInstance inferInstance hκ
  obtain ⟨M, hM⟩ := complexGodementStandardConvergence n hn (List.ofFn es) (by simp)
  let B₀ : ℝ := (n : ℝ) + M - (((n : ℂ) + 1) / 2).re
  let B₁ : ℝ := ∑ j, |(es j).exponent.re|
  refine ⟨max B₀ B₁, fun d Φ f hf g => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hTate d es Φ f hf g
  obtain ⟨N₀, hN₀, hEqN₀⟩ := complexTateProductContinuation n Ψ (angular d es) (offset d es) 1
  let pref (s : ℂ) := characterWeight (characterOfParams d.weight (d.exponent + s)) ((n : ℂ) / 2)
    (determinant g)
  let N (s : ℂ) := pref s * ((c : ℂ) * N₀ s)
  let D := (godementLFactor d es).denominator
  have hN : Differentiable ℂ N := (differentiable_characterWeight_exponent d _ _).mul (hN₀.const_mul _)
  have hZ : Meromorphic (fun s => N s / D s) := by
    intro s
    exact (hN.analyticAt s).meromorphicAt.div ((godementLFactor d es).entire.analyticAt s).meromorphicAt
  refine ⟨N, fun s => N s / D s, hN, hZ, fun _ => rfl, fun s hs => ?_⟩
  let dₛ := characterOfParams d.weight (d.exponent + s)
  have hs₀ : B₀ < d.exponent.re + s.re := (le_max_left _ _).trans_lt hs
  have hs₁ : B₁ < d.exponent.re + s.re := (le_max_right _ _).trans_lt hs
  have hI := hM dₛ Φ f hf (by
    dsimp only [dₛ]
    rw [characterOfParams_exponent, Complex.add_re, Complex.add_re]
    dsimp only [B₀] at hs₀
    linarith) g
  have hpos (j : Fin n) : 0 < (affineParameter (offset d es) 1 s j).re := by
    have hsum := Finset.single_le_sum (f := fun k => |(es k).exponent.re|)
      (fun k _ => abs_nonneg (es k).exponent.re) (Finset.mem_univ j)
    have hbound := (le_abs_self (es j).exponent.re).trans hsum
    simp only [affineParameter, offset, Pi.one_apply, Complex.ofReal_one, one_mul, Complex.add_re,
      Complex.sub_re, Complex.one_re]
    dsimp only [B₁] at hs₁
    linarith
  have hD : D s ≠ 0 := godementLFactor_denominator_ne_zero d es s hpos
  refine ⟨hI, hD, ?_⟩
  apply (div_eq_iff hD).mpr
  change pref s * ((c : ℂ) * N₀ s) = godementSection μ dₛ Φ f g * D s
  rw [hEqN₀ s hpos, normalizedZeta, ← godementLFactor_denominator, godementSection, hΨ s hI]
  let A := ComplexTateProduct.zeta Ψ (angular d es) (affineParameter (offset d es) 1 s)
  change pref s * ((c : ℂ) * (D s * A)) = pref s * ((c : ℂ) * A) * D s
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
