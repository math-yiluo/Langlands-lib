import Langlands.Global.RankinSelberg.ComplexJacquetCanonicalSmooth
import Langlands.Global.RankinSelberg.ComplexLocalIntertwinerAnalytic
import Langlands.Global.RankinSelberg.ComplexLocalAnalyticRightJet
import Langlands.Global.RankinSelberg.ComplexMatrixConnected

/-! # The canonical complex Jacquet range and identity evaluations -/

noncomputable section

open scoped TensorProduct ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (characterOfParams borelFactor borelFactor_eq_cpow matrixModel
  unitsExtension unitsExtension_add unitsExtension_smul rightDerivative rightDerivative_add rightDerivative_smul
  complexStandardLie envelopingAction)
open Langlands.Archimedean.ComplexLocalCasimir (realGenerator realGenerator_action)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquet (complexLocalAnalyticRightJet)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}
local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "Std[" d "]" => Automorphic.complexStandardKFinite n d
local notation "J" => matrixModel ℂ n
local notation "D" => rightDerivative J
local notation "WMap[" d "]" => (Std[d] →ₗ[ℂ] (G → ℂ))

/-- Every list of the indicated length comes from its angular weights and radial exponents. -/
theorem exists_characterList_of_length {j : ℕ} (d : List ComplexCharacterData) (h : d.length = j) :
    ∃ (l : Fin j → ℤ) (p : Fin j → ℂ), characterList l p = d := by
  subst j
  refine ⟨fun i => (d.get i).weight, fun i => (d.get i).exponent, ?_⟩
  calc
    _ = List.ofFn d.get := congrArg List.ofFn (funext fun i => Langlands.Archimedean.characterOfParams_eta (d.get i))
    _ = d := List.ofFn_get d

/-- Proportional identity evaluations give proportional intertwiners. -/
theorem complexWhittaker_eq_smul_of_eval_one {d : List ComplexCharacterData} {a : ℂˣ}
    {B C : WMap[d]} (hB : IsComplexWhittakerIntertwiner r d a B)
    (hC : IsComplexWhittakerIntertwiner r d a C) (c : ℂ)
    (h₁ : ∀ f, B f 1 = c * C f 1) : B = c • C := by
  let A (f : Std[d]) : G → ℂ := B f + (-c) • C f
  let R (X : M) := envelopingAction (complexStandardLie n d) (realGenerator n X)
  have hs (f : Std[d]) : ContMDiff J 𝓘(ℝ, ℂ) ∞ ((-c) • C f) :=
    (((-c) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp (hC.2.1 f)
  have hAn (f : Std[d]) : AnalyticOnNhd ℝ (unitsExtension (A f)) {y : M | IsUnit y} := by
    have he : unitsExtension (A f) = fun y => unitsExtension (B f) y + (-c) * unitsExtension (C f) y := by
      funext y
      dsimp only [A]
      rw [unitsExtension_add, unitsExtension_smul]
    rw [he]
    exact (analyticOnNhd_unitsExtension_complexWhittaker hB f).add
      (analyticOnNhd_const.mul (analyticOnNhd_unitsExtension_complexWhittaker hC f))
  have hD (X : M) (f : Std[d]) : D X (A f) = A (R X f) := by
    change D X (B f + (-c) • C f) = B (R X f) + (-c) • C (R X f)
    rw [rightDerivative_add (hB.2.1 f) (hs f), rightDerivative_smul (hC.2.1 f),
      hB.2.2.2.2 X f (R X f) (realGenerator_action d X f),
      hC.2.2.2.2 X f (R X f) (realGenerator_action d X f)]
  have h0 (f : Std[d]) : A f 1 = 0 := by
    change B f 1 + (-c) * C f 1 = 0
    rw [h₁ f, neg_mul, add_neg_cancel]
  have hz := @complexLocalAnalyticRightJet (r + 1) (isPreconnected_complexMatrixUnits n)
    (Std[d]) A (fun X f => R X f) 1 (fun f => (hB.2.1 f).add (hs f)) hAn hD h0
  ext f g
  have h := hz f g
  change B f g + (-c) * C f g = 0 at h
  change B f g = c * C f g
  simpa only [neg_mul, ← sub_eq_add_neg, sub_eq_zero] using h

/-- The remaining scalar comparison of identity evaluations, with the inducing characters
in fixed compact coordinates. -/
def ComplexJacquetIdentityProportionality : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ)
    (B : Automorphic.complexStandardKFinite (r + 1) (characterList l p) →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)),
    IsComplexWhittakerIntertwiner r (characterList l p) (-a) B →
    ∃ c : ℂ, ∀ f, B f 1 = c * continuedJacquet μ a l p f 1

/-- Under scalar comparison of the identity evaluations the exact model in every rank is the
range of the canonical continuation for any scalar additive Haar measure. -/
def ComplexJacquetCanonicalRangeStatement : Prop :=
  ComplexJacquetIdentityProportionality →
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : List ComplexCharacterData),
    d.length = r + 1 →
    ∃ (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ), characterList l p = d ∧
      complexWhittakerModel r d (-a) = LinearMap.range (continuedJacquet μ a l p)

theorem complexJacquetCanonicalRange : ComplexJacquetCanonicalRangeStatement := by
  intro h r μ a d hd
  obtain ⟨l, p, rfl⟩ := exists_characterList_of_length d hd
  let C := continuedJacquet μ a l p
  have hC := complexJacquetCanonicalIntertwiner μ a l p
  refine ⟨l, p, rfl, le_antisymm ?_ ?_⟩
  · apply iSup_le
    intro B
    apply iSup_le
    intro hB
    obtain ⟨c, hc⟩ := h r μ a l p B hB
    rw [complexWhittaker_eq_smul_of_eval_one hB hC c hc]
    rintro _ ⟨f, rfl⟩
    exact ⟨c • f, C.map_smul c f⟩
  · exact (le_iSup (fun h : IsComplexWhittakerIntertwiner r (characterList l p) (-a) C => LinearMap.range C) hC).trans
      (le_iSup (fun B : Automorphic.complexStandardKFinite (r + 1) (characterList l p) →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℂ → ℂ) =>
        ⨆ _ : IsComplexWhittakerIntertwiner r (characterList l p) (-a) B, LinearMap.range B) C)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
