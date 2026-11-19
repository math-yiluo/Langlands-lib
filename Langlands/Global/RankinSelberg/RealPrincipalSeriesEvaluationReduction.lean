import Langlands.Global.RankinSelberg.RealPrincipalSeriesSmoothCoefficient
import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerReduction
import Langlands.Global.RankinSelberg.RealWhittakerEvaluation

/-! # Extension of real Whittaker coefficient maps from scalar evaluation data -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPrincipalSeries

variable (r : ℕ) (ds : List RealBlock)

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "V" => Automorphic.realStandardKFinite (r + 1) ds
local notation "P" => principalSeries ℝ (r + 1) (realPositionCharacter (expand ds))

/-- Include the original K-finite source in the smooth expanded principal series. -/
def expandedSmoothInclusion : V →ₗ[ℂ] P :=
  Submodule.inclusion fun _ hf => (realStandardKFinite_le_expand (r + 1) ds hf).1.1

private theorem translate_one (x : P) : translate r (expand ds) 1 x = x := by
  apply Subtype.ext
  funext g
  change x.val (g * 1) = x.val g
  rw [mul_one]

end RealPrincipalSeries

open RealPrincipalSeries

/-- On an inducing list with a nonzero weight, the identity evaluation of a uniform
coefficient map has a derivative-bounded Whittaker extension to the smooth position
principal series of the expanded list. -/
def RealUniformPrincipalSeriesEvaluationExtensionStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    (∃ p d, realInducedBlockAt ds p = some d ∧ d.weight ≠ 0) →
  ∀ (a : ℝˣ) (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
    (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealUniformWhittakerIntertwiner r ds a B →
      ∃ ℓ : principalSeries ℝ (r + 1) (realPositionCharacter (expand ds)) →ₗ[ℂ] ℂ,
        HasCompactDerivativeBound r (expand ds) ℓ ∧
        (∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ,
          ∀ x : principalSeries ℝ (r + 1) (realPositionCharacter (expand ds)),
            ℓ (translate r (expand ds) u x) = realWhittakerCharacter a u * ℓ x) ∧
        ∀ f, ℓ (expandedSmoothInclusion r ds f) = B f 1

/-- Bounded equivariant extension of every identity evaluation implies extension of
the uniform coefficient maps themselves. -/
def RealUniformPrincipalSeriesEvaluationReductionStatement : Prop :=
  RealUniformPrincipalSeriesEvaluationExtensionStatement →
    RealUniformPrincipalSeriesExtensionStatement

theorem realUniformPrincipalSeriesEvaluationReduction :
    RealUniformPrincipalSeriesEvaluationReductionStatement := by
  intro h r ds hr hWeight a B hB
  obtain ⟨ℓ, hℓ, hψ, hEval⟩ := h r ds hr hWeight a B hB
  let C := functionalCoefficient (expand ds) ℓ
  have hC := compactWhittakerCoefficient r (expand ds) a ℓ hℓ hψ
  refine ⟨C, hC, ?_⟩
  let ι := Submodule.inclusion (realStandardKFinite_le_expand (r + 1) ds)
  have hRestrict : IsRealWhittakerIntertwiner r ds a (C.comp ι) := by
    obtain ⟨hN, hSmooth, hGrowth, hK, hLie⟩ := hC.1
    exact ⟨fun f => hN (ι f), fun f => hSmooth (ι f), fun f => hGrowth (ι f),
      fun k f f' hf => hK k (ι f) (ι f') hf, fun X f f' hf => hLie X (ι f) (ι f') hf⟩
  apply realWhittakerEvaluation r ds a (C.comp ι) B hRestrict hB.1
  intro f
  change ℓ (translate r (expand ds) 1 (expandedSmoothInclusion r ds f)) = B f 1
  rw [translate_one]
  exact hEval f

end Langlands.Global.RankinSelbergGlobal
