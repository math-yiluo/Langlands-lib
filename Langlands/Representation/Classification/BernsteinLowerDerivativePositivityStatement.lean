import Langlands.Representation.Classification.BernsteinDerivativePositivity
import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeOrder
import Langlands.Representation.Unitary.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! # Lower shifted-derivative positivity for irreducible unitary representations -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The necessary lower-derivative positivity in Bernstein's unitary criterion,
including order zero. This is a statement, not a proof of that analytic input. -/
def BernsteinUnitaryLowerDerivativePositivity : Prop :=
  letI := T.topology
  ∀ (N : ℕ), 0 < N →
    ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      Representation.IsIrreducible π.representation →
      IsUnitarizable π.representation →
      ∀ hd : Derivative.GeneralLinearHighestDerivativeOrderData T ψ π,
        BernsteinShiftedDerivativePositiveBelow T ψ π hd.order

end Langlands.Classification
