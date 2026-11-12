import Langlands.Representation.RankinSelberg.HighlyRamified.ZeroCellLift
import Langlands.Representation.Conductor.SphericalTranslation

/-!
# The corank-one integral of a translated zero-cell function

Let `W` agree with the zero-cell function `W₀` on the mirabolic subgroup of
`GL_(n+2)(F)`, and let `X` be a right `GL_(n+1)(O)`-invariant inverse Whittaker function
with `X(1) = 1` which transforms under right translation by `a⁻¹` by a scalar `κ`. Then
the corank-one integral of the right translate of `W` by `diag(a, 1)` against `X`
converges for every `s` and equals `κ |det a|^(-(s - 1/2))`: substituting `g ↦ g a⁻¹` in
the quotient `N \ GL_(n+1)` reduces it to the corank-one integral of `W₀` against `X`,
which is `1`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open Langlands.GeneralLinear.Iwasawa

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The corank-one integral of the translate of a zero-cell lift by `diag(a, 1)` against
an integral-invariant inverse Whittaker function `X` with `X(1) = 1` and
`X(g a⁻¹) = κ X(g)` converges for every `s` and equals `κ |det a⁻¹|^(s - 1/2)`. -/
theorem zeroCell_translate_corankOne (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
    ∀ {ϖ : F.Carrierˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
      {ψ : UnitaryAdditiveCharacter F.Carrier}
      (hψ : ∀ x ∈ (ValuativeRel.valuation F.Carrier).integer, ψ x = 1)
      (W : WhittakerFunctions ψ (n + 1)),
      (∀ g : Langlands.GeneralLinear (n + 1 + 1) F.Carrier,
        (∀ j, g.val (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then 1 else 0) →
        W.val g = (zeroCellWhittaker hϖ hψ (n + 1)).val g) →
    ∀ (X : InverseWhittakerFunctions ψ n),
      (∀ g k, k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
        X.val (g * k) = X.val g) →
      X.val 1 = 1 →
    ∀ (a : Langlands.GeneralLinear (n + 1) F.Carrier) (κ : ℂ),
      (∀ g, X.val (g * a⁻¹) = κ * X.val g) → ∀ s : ℂ,
      Integrable (corankOneIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        (translateWhittaker ψ (n + 1) W (rankInclusion 1 a)) X s) μ ∧
      corankOneIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData) μ
        (translateWhittaker ψ (n + 1) W (rankInclusion 1 a)) X s =
        κ * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) a⁻¹
          (s - 1 / 2) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro μ hμ ϖ hϖ ψ hψ W hW X hX hX1 a κ hXa s
  obtain ⟨hint, hval⟩ :=
    integrable_integral_corankOneIntegrand_zeroCell F n μ hμ hϖ hψ X hX hX1 s
  let abv := normalizedAbsoluteValue T
  have he : corankOneIntegrand ψ abv (translateWhittaker ψ (n + 1) W (rankInclusion 1 a)) X s =
      fun x => (κ * determinantWeight abv a⁻¹ (s - 1 / 2)) *
        corankOneIntegrand ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) X s
          (rightTranslate (upperUnipotent (n + 1) F.Carrier) a x) := by
    funext x
    induction x using Quotient.inductionOn with
    | h g =>
      rw [rightTranslate_mk, corankOneIntegrand_mk, corankOneIntegrand_mk,
        translateWhittaker_apply, ← map_mul, hW _ (rankInclusion_lastRow _)]
      have hXg : X.val g = κ * X.val (g * a) := by rw [← hXa, mul_inv_cancel_right]
      have hd : determinantWeight abv g (s - 1 / 2) =
          determinantWeight abv (g * a) (s - 1 / 2) * determinantWeight abv a⁻¹ (s - 1 / 2) := by
        rw [← Conductor.determinantWeight_mul, mul_inv_cancel_right]
      rw [hXg, hd]
      ring
  have hmp := hμ.right_invariant a
  have hemb := (rightTranslate (upperUnipotent (n + 1) F.Carrier) a).measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [he]
    exact ((hmp.integrable_comp_emb hemb).mpr hint).const_mul _
  · unfold corankOneIntegral
    rw [he, integral_const_mul, hmp.integral_comp hemb, hval, mul_one]

end Langlands.RankinSelberg.HighlyRamified
