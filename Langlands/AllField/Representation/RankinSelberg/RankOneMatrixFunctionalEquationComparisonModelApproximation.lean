import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelApproximation
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Group.GL.PadicBlocksSupplement
/-! # Compact approximation for actual smooth coefficient-model vectors -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.CompactWhittakerApproximation
open Langlands.RankinSelberg.CompactWhittakerApproximation hiding modelApproximationGLBorel modelApproximationGLLocallyCompact modelApproximationGLMeasurable modelApproximationGLNonarchimedean modelApproximationGLSigmaCompact modelApproximationLocalField modelApproximationT2 modelApproximationTopology modelApproximationValuativeRel weighted_glModel_integral_eq_of_compact
open Langlands.AllField.RankinSelberg.CompactWhittakerApproximation
open Langlands.RankinSelberg
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.Whittaker
open Langlands.Induction hiding SmoothRep
open Langlands.GeneralLinear

universe uG uR uV uA uB uF

section ModelInclusion


end ModelInclusion

section ModelComparison


end ModelComparison

section CanonicalPadic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelApproximationT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance modelApproximationGLNonarchimedean (n : ℕ) :
    NonarchimedeanGroup (Langlands.GeneralLinear (n + 1) F) :=
  valuativeGeneralLinearNonarchimedean F (n + 1)
local instance modelApproximationGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance modelApproximationGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (n + 1)
local instance modelApproximationGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance modelApproximationGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {A : Type uA} {B : Type uB} [MeasurableSpace A] [MeasurableSpace B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Canonical p-adic GL specialization for an actual Whittaker model, using
only smoothness of the original representation and the two weighted bounds. -/
theorem weighted_glModel_integral_eq_of_compact
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F) (n : ℕ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ n π)
    (μ : Measure A) (ν : Measure B)
    (ρ : A → Langlands.GeneralLinear (n + 1) F)
    (τ : B → Langlands.GeneralLinear (n + 1) F)
    (w : A → ℂ) (v : B → ℂ) (hρ : Measurable ρ) (hτ : Measurable τ)
    (hcompact : ∀ f : CompactFunctions (upperUnipotent (n + 1) F)
        (characterRepresentation (standardCharacter ψ n)),
      (∫ a, w a * eval _ _ f.val (ρ a) ∂μ) =
      ∫ b, v b * eval _ _ f.val (τ b) ∂ν)
    (f : (glCoefficientModel ψ n π ℓ).toSubmodule)
    (hi : Integrable (fun a => w a * glModelFunction ψ n π ℓ f (ρ a)) μ)
    (hj : Integrable (fun b => v b * glModelFunction ψ n π ℓ f (τ b)) ν) :
    (∫ a, w a * glModelFunction ψ n π ℓ f (ρ a) ∂μ) =
      ∫ b, v b * glModelFunction ψ n π ℓ f (τ b) ∂ν :=
  weighted_model_integral_eq_of_compact μ ν (upperUnipotent (n + 1) F)
    UpperUnipotent.isClosed (standardCharacter ψ n) π hπ ℓ
    ρ τ w v hρ hτ hcompact f hi hj

end CanonicalPadic

end Langlands.AllField.RankinSelberg.CompactWhittakerApproximation
