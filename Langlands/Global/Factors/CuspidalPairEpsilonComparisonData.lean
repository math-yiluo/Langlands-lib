import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Global.Factors.RelativeWeilEngine
import Langlands.LocalFactor.Archimedean.GammaExponentComparison
import Langlands.LocalFactor.ArchimedeanPairFactor
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # Cuspidal pair data for comparing the finite epsilon bases -/

noncomputable section

open Filter Topology
open scoped BigOperators Topology

namespace Langlands.LocalFactor.Archimedean

/-- The number of real Gamma factors of a real pair is the product of the
ranks of its standard-module presentations. -/
theorem realPairGammaCount (xs ys : List RealBlock) :
    (((realPairBlocks xs ys).map RealBlock.gammaBlock).flatMap GammaBlock.realShifts).length =
      realRank xs * realRank ys := by
  rw [← realRank_realPairBlocks]
  generalize realPairBlocks xs ys = blocks
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
    cases b with
    | character d => simp [RealBlock.gammaBlock, GammaBlock.realShifts, RealBlock.rank, ih, add_comm]
    | induced d =>
      simp [RealBlock.gammaBlock, GammaBlock.realShifts, RealBlock.rank, ih]
      omega

/-- The complex pair contributes two real Gamma factors per character block. -/
theorem complexPairGammaCount (xs ys : List ComplexCharacterData) :
    (((complexPairBlocks xs ys).map ComplexCharacterData.gammaBlock).flatMap
      GammaBlock.realShifts).length = 2 * (xs.length * ys.length) := by
  rw [← length_complexPairBlocks]
  generalize complexPairBlocks xs ys = blocks
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
    simp [ComplexCharacterData.gammaBlock, GammaBlock.realShifts, ih, Nat.mul_succ, add_comm]
    omega

/-- The part of the real-pair epsilon factor varying with `z` depends only on
its pair rank and the absolute value of the additive-character scale. -/
theorem realPairEpsilon_eq_at_zero_mul_cpow (xs ys : List RealBlock) (a : ℝˣ) (c : NNReal)
    (hc : 0 < c) (z : ℂ) :
    (realPairEpsilon xs ys a c hc z : ℂ) = (realPairEpsilon xs ys a c hc 0 : ℂ) *
      ((|(a : ℝ)| : ℝ) : ℂ) ^ (((realRank xs * realRank ys : ℕ) : ℂ) * z) := by
  have ha : ((|(a : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr a.ne_zero)
  simp only [realPairEpsilon, coe_realEpsilon, realRank_realPairBlocks]
  rw [mul_sub, Complex.cpow_sub _ _ ha]
  simp only [zero_sub, mul_neg, mul_one, Complex.cpow_neg]
  ring

/-- The part of the complex-pair epsilon factor varying with `z` uses twice
the pair rank and the absolute value of the additive-character scale. -/
theorem complexPairEpsilon_eq_at_zero_mul_cpow (xs ys : List ComplexCharacterData) (a : ℂˣ)
    (c : NNReal) (hc : 0 < c) (z : ℂ) :
    (complexPairEpsilon xs ys a c hc z : ℂ) = (complexPairEpsilon xs ys a c hc 0 : ℂ) *
      (‖(a : ℂ)‖ : ℂ) ^ (2 * ((xs.length * ys.length : ℕ) : ℂ) * z) := by
  have ha : (‖(a : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero)
  simp only [complexPairEpsilon, coe_complexEpsilon, length_complexPairBlocks]
  rw [mul_sub, Complex.cpow_sub _ _ ha]
  simp only [zero_sub, mul_neg, mul_one, Complex.cpow_neg]
  ring

private theorem exists_gammaBlockDenominator_ne_zero (b : GammaBlock) :
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → b.factor.denominator z ≠ 0 := by
  cases b with
  | real a =>
    refine ⟨-a.re, fun z hz => inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ?_)⟩
    rw [Complex.add_re]
    linarith
  | complex a =>
    refine ⟨-a.re, fun z hz => inv_ne_zero ?_⟩
    change Complex.Gammaℂ (z + a) ≠ 0
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    apply mul_ne_zero <;> apply Complex.Gammaℝ_ne_zero_of_re_pos <;>
      simp only [Complex.add_re, Complex.one_re] <;> linarith

/-- A finite product of the archimedean Gamma factors has no poles on some
right half-plane. -/
theorem exists_gammaProductDenominator_ne_zero (blocks : List GammaBlock) :
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → (gammaProduct blocks).denominator z ≠ 0 := by
  induction blocks with
  | nil => exact ⟨0, fun _ _ => one_ne_zero⟩
  | cons b blocks ih =>
    obtain ⟨σ, hσ⟩ := exists_gammaBlockDenominator_ne_zero b
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨max σ τ, fun z hz => ?_⟩
    change (b.factor.mul (gammaProduct blocks)).denominator z ≠ 0
    rw [ReciprocalEntire.denominator_mul]
    exact mul_ne_zero (hσ z (lt_of_le_of_lt (le_max_left _ _) hz))
      (hτ z (lt_of_le_of_lt (le_max_right _ _) hz))

end Langlands.LocalFactor.Archimedean

namespace Langlands.Global.CuspidalPairFunctionalEquation.FinitePairFactorChoice

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open FunctionalEquationComparison RelativeWeilEngine LocalFactor.Archimedean

universe u uQ

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T Td : CuspidalOperatorRealization F r} {T' Td' : CuspidalOperatorRealization F t}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
  {P' : CuspidalSpectralPresentation.{u, uQ} T'} {Pd' : CuspidalSpectralPresentation.{u, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}

private theorem ne_zero_of_hasProd_of_summable_norm_sub_one {ι : Type*} {f : ι → ℂ} {p : ℂ}
    (hp : HasProd f p) (hs : Summable (fun i => ‖f i - 1‖)) (h : ∀ i, f i ≠ 0) : p ≠ 0 := by
  have hn := tprod_one_add_ne_zero_of_summable (f := fun i => f i - 1)
    (fun i => by simpa only [add_sub_cancel] using h i) hs
  have he : (fun i => 1 + (f i - 1)) = f := by
    funext i
    ring
  rw [he, hp.tprod_eq] at hn
  exact hn

/-- A completed cuspidal pair equation with nonvanishing finite factors on a
right half-plane supplies the Library's package for multiplying and comparing
functional equations. The new meromorphic functions are the completed ones
multiplied by the corresponding entire archimedean denominators. -/
theorem hasGlobalEquation_of_completedEquation
    (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')
    (S : Finset (FinitePlace F)) (A Ad : List GammaBlock) (Ae : ℂ → ℂ)
    (hFE : c.CompletedEquationHolds S (fun z => ((gammaProduct A).denominator z)⁻¹)
      (fun z => ((gammaProduct Ad).denominator z)⁻¹) Ae)
    (hreg : ∃ τ : ℝ, ∀ z : ℂ, τ < z.re →
      (∀ v, c.finiteL v z ≠ 0) ∧ (∀ v, c.finiteDualL v z ≠ 0)) :
    HasGlobalEquation c.finiteL c.finiteDualL c.finiteEpsilon
      (fun z => ((gammaProduct A).denominator z)⁻¹)
      (fun z => ((gammaProduct Ad).denominator z)⁻¹) Ae S := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hprod, hfe⟩ := hFE
  obtain ⟨τ, hτ⟩ := hreg
  obtain ⟨α, hα⟩ := exists_gammaProductDenominator_ne_zero A
  obtain ⟨αd, hαd⟩ := exists_gammaProductDenominator_ne_zero Ad
  let D := gammaProduct A
  let Dd := gammaProduct Ad
  refine ⟨max (max σ τ) (max α αd), fun z => Λ z * D.denominator z,
    fun z => Λd z * Dd.denominator z,
    fun z => (hΛ z (Set.mem_univ z)).mul (D.entire.analyticAt z).meromorphicAt,
    fun z => (hΛd z (Set.mem_univ z)).mul (Dd.entire.analyticAt z).meromorphicAt, ?_, ?_⟩
  · intro z hz
    have hz₁ := lt_of_le_of_lt (le_max_left (max σ τ) (max α αd)) hz
    have hz₂ := lt_of_le_of_lt (le_max_right (max σ τ) (max α αd)) hz
    obtain ⟨hs, hsd, p, pd, hp, hpd, hzΛ, hzΛd⟩ := hprod z
      (lt_of_le_of_lt (le_max_left _ _) hz₁)
    obtain ⟨hzr, hzrd⟩ := hτ z (lt_of_le_of_lt (le_max_right _ _) hz₁)
    have hval : Λ z * D.denominator z = p := by
      rw [hzΛ, mul_comm _ p, mul_assoc,
        inv_mul_cancel₀ (hα z (lt_of_le_of_lt (le_max_left _ _) hz₂)), mul_one]
    have hvald : Λd z * Dd.denominator z = pd := by
      rw [hzΛd, mul_comm _ pd, mul_assoc,
        inv_mul_cancel₀ (hαd z (lt_of_le_of_lt (le_max_right _ _) hz₂)), mul_one]
    dsimp only
    rw [hval, hvald]
    exact ⟨⟨hp, ne_zero_of_hasProd_of_summable_norm_sub_one hp hs hzr⟩,
      hpd, ne_zero_of_hasProd_of_summable_norm_sub_one hpd hsd hzrd⟩
  · intro w
    filter_upwards [meromorphicEq_of_codiscrete hfe w, D.denominator_eventually_ne_zero w,
      (reflection_tendsto w).eventually (Dd.denominator_eventually_ne_zero (1 - w))]
      with z hz hD hDd
    change (Λ z * D.denominator z) * (D.denominator z)⁻¹ =
      Ae z * (∏ v ∈ S, c.finiteEpsilon v z) *
        ((Λd (1 - z) * Dd.denominator (1 - z)) * (Dd.denominator (1 - z))⁻¹)
    rw [mul_inv_cancel_right₀ hD, mul_inv_cancel_right₀ hDd, hz, mul_comm (Ae z)]

end Langlands.Global.CuspidalPairFunctionalEquation.FinitePairFactorChoice
