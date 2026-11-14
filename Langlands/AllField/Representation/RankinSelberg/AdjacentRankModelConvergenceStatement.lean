import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankIntegralModel
/-!
# Unconditional convergence of the JPSS Section 6.1 tensor integral

This is the convergence assertion of the Proposition in JPSS Section 6.1,
printed pp.428–429, for formula (8). It uses the published special lower-block
model unchanged and quantifies over the entire algebraic tensor test space.
The large-positive-twist restriction concerns the separate induced-model
spanning assertion. This module defines an unproved proposition.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

/-- JPSS Section 6.1, formula (8): every test tensor has an integrable scalar
integrand at every ambient element, for every quasicharacter and every supplied
self-dual scalar Haar measure, when the inner representation has full standard
Whittaker type. The conclusion uses exactly the canonical p-adic model and its
shared Haar measure. This definition supplies no convergence proof. -/
def AdjacentRankModelConvergenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : AdditiveHaarMeasure F) (hself : IsSelfDual ψ ν)
      (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (GeneralLinear (r + 1) F) V),
      IsOfWhittakerType r (standardCharacter ψ r) σ →
      ∀ (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
        (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F),
        Langlands.AllField.RankinSelberg.Padic.AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ g

end Langlands.AllField.RankinSelberg
