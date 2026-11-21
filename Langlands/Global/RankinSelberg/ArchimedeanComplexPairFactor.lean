import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction

/-! # Rapidly decreasing Mellin pairs for the complex Rankin–Selberg factors -/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology Real

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanComplexPairFactor

open Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair ArchimedeanInverseMellin

theorem lFactor_stripExpType (d : ComplexCharacterData) : StripExpType d.lFactor.denominator :=
  inv_Gammaℂ_stripExpType.comp_add (d.exponent + (d.weight.natAbs : ℂ) / 2)

theorem complexLFactor_stripExpType (ds : List ComplexCharacterData) :
    StripExpType (complexLFactor ds).denominator :=
  (StripExpType.list_prod ds (fun d => d.lFactor.denominator)
    fun d _ => lFactor_stripExpType d).congr fun s => (denominator_complexLFactor ds s).symm

private theorem lFactor_ne_zero (d : ComplexCharacterData) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → d.lFactor.denominator s ≠ 0 := by
  let v := d.exponent + (d.weight.natAbs : ℂ) / 2
  refine ⟨-v.re, fun s hs => ?_⟩
  change (Complex.Gammaℂ (s + v))⁻¹ ≠ 0
  apply inv_ne_zero
  have hpos : 0 < (s + v).re := by rw [Complex.add_re]; linarith
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hpos)
  exact Complex.cpow_ne_zero_iff.mpr (.inl (by
    exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)))

theorem complexLFactor_ne_zero (ds : List ComplexCharacterData) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (complexLFactor ds).denominator s ≠ 0 := by
  induction ds with
  | nil => exact ⟨0, fun s _ => by simp [Langlands.LocalFactor.ReciprocalEntire.one]⟩
  | cons d ds ih =>
    obtain ⟨σ₁, h₁⟩ := lFactor_ne_zero d
    obtain ⟨σ₂, h₂⟩ := ih
    refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
    rw [denominator_complexLFactor, List.map_cons, List.prod_cons, ← denominator_complexLFactor]
    exact mul_ne_zero (h₁ s ((le_max_left _ _).trans_lt hs))
      (h₂ s ((le_max_right _ _).trans_lt hs))

theorem epsilon_stripExpType (d : ComplexCharacterData) (a : ℂˣ) (c : ℝ≥0) (hc : 0 < c) :
    StripExpType (fun s => (d.epsilon a c hc s : ℂ)) := by
  have ha : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  have h := ((StripExpType.ofReal_cpow ha).comp_ofReal_mul 2).comp_add (-1)
  refine (((StripExpType.const ((c : ℂ) * (d.character a : ℂ))).mul h).mul
    (StripExpType.const (Complex.I ^ d.weight.natAbs))).congr fun s => ?_
  rw [ComplexCharacterData.coe_epsilon]
  simp only [Complex.ofReal_ofNat, sub_eq_add_neg]

theorem complexEpsilon_stripExpType (ds : List ComplexCharacterData) (a : ℂˣ) (c : ℝ≥0) (hc : 0 < c) :
    StripExpType (fun s => (complexEpsilon ds a c hc s : ℂ)) := by
  induction ds with
  | nil => exact (StripExpType.const 1).congr fun s => by simp [complexEpsilon]
  | cons d ds ih =>
    exact ((epsilon_stripExpType d a c hc).mul ih).congr fun s => by simp [complexEpsilon]

/-- The entire reciprocal gamma products give rapidly decreasing radial Mellin pairs.
The two Mellin transforms are nonzero in a right half-plane. -/
def ComplexPairMellinFactorStatement : Prop :=
  ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ),
    sign ≠ 0 → ∃ (σ : ℝ) (h k : ℝ → ℂ),
      Measurable h ∧ Measurable k ∧ RapidDecay h ∧ RapidDecay k ∧
      (∀ s : ℂ, mellin h (-s) = sign * (complexPairEpsilon ds es a c hc s : ℂ) *
        Complex.exp (s ^ 2) * (complexPairLFactor ds es).denominator s) ∧
      (∀ s : ℂ, mellin k (s - 1) = Complex.exp (s ^ 2) *
        (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator (1 - s)) ∧
      (∀ s : ℂ, σ < s.re → mellin h (-s) ≠ 0) ∧
      (∀ s : ℂ, σ < s.re → mellin k (-s) ≠ 0) ∧
      ∀ᶠ s in codiscrete ℂ,
        ((complexPairLFactor ds es).denominator s)⁻¹ * mellin h (-s) =
          sign * (complexPairEpsilon ds es a c hc s : ℂ) *
            ((complexPairLFactor (ds.map ComplexCharacterData.inv)
              (es.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * mellin k (s - 1)

theorem complexPairMellinFactor : ComplexPairMellinFactorStatement := by
  intro ds es a c hc sign hsign
  let xs := complexPairBlocks ds es
  let ys := complexPairBlocks (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
  obtain ⟨σ₁, hσ₁⟩ := complexLFactor_ne_zero xs
  obtain ⟨σ₂, hσ₂⟩ := complexLFactor_ne_zero ys
  obtain ⟨h, k, hh, hk, hhd, hkd, hhM, hkM, hnzh, hnzk, hEq⟩ :=
    exists_factor_pair (D := (complexLFactor xs).denominator) (Dd := (complexLFactor ys).denominator)
      (E := fun s => (complexEpsilon xs a c hc s : ℂ))
      (complexLFactor xs).entire (complexLFactor ys).entire
      (differentiable_complexEpsilon xs a c hc) (complexLFactor_stripExpType xs)
      (complexLFactor_stripExpType ys) (complexEpsilon_stripExpType xs a c hc) hsign
      (σ₀ := max σ₁ σ₂) (fun s hs => ⟨hσ₁ s ((le_max_left _ _).trans_lt hs),
        hσ₂ s ((le_max_right _ _).trans_lt hs), (complexEpsilon xs a c hc s).ne_zero⟩)
  exact ⟨max σ₁ σ₂, h, k, hh, hk, hhd, hkd, hhM, hkM, hnzh, hnzk, hEq⟩

end Langlands.Global.RankinSelbergGlobal.ArchimedeanComplexPairFactor
