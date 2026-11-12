import Langlands.Representation.Classification.BernsteinDerivativePositivity
import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeOrder
import Langlands.Representation.Unitary.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! # A unitary finite-length highest-derivative irreducibility criterion -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A sufficient unitary specialization of Bernstein's finite-length
irreducibility criterion. Every hypothesis refers to the actual representation
or its actual shifted derivatives. -/
def BernsteinUnitaryFiniteLengthIrreducibilityCriterion : Prop :=
  letI := T.topology
  ∀ (N : ℕ), 0 < N →
    ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
      (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      A.HasFiniteLength →
      IsUnitarizable A.representation →
      ∀ hd : Derivative.GeneralLinearHighestDerivativeOrderData T ψ A,
        BernsteinShiftedDerivativePositiveBelow T ψ A hd.order →
        Representation.IsIrreducible
          (bernsteinShiftedDerivative T ψ A hd.order hd.le_rank).representation →
        IsUnitarizable
          (bernsteinShiftedDerivative T ψ A hd.order hd.le_rank).representation →
        Representation.IsIrreducible A.representation

end Langlands.Classification
