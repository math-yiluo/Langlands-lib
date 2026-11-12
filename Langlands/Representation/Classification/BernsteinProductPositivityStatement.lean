import Langlands.Representation.Classification.BernsteinDerivativePositivity
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Unitary.Basic

/-! # Positivity of binary products with unitary top shifted derivatives -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The product-positivity implication used in Bernstein's rank induction.
The supplied bounds may be zero, so this also covers rank-zero factors. -/
def BernsteinUnitaryTopDerivativeProductPositivity : Prop :=
  letI := T.topology
  ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
    A.HasFiniteLength →
    B.HasFiniteLength →
    ∀ (r s : ℕ) (hr : r ≤ a) (hs : s ≤ b),
      (∀ (j : ℕ) (hj : j ≤ a), r < j →
        Subsingleton ((Derivative.generalLinearDerivative T ψ a j hj).obj A)) →
      (∀ (j : ℕ) (hj : j ≤ b), s < j →
        Subsingleton ((Derivative.generalLinearDerivative T ψ b j hj).obj B)) →
      BernsteinShiftedDerivativePositiveBelow T ψ A r →
      BernsteinShiftedDerivativePositiveBelow T ψ B s →
      IsUnitarizable (bernsteinShiftedDerivative T ψ A r hr).representation →
      IsUnitarizable (bernsteinShiftedDerivative T ψ B s hs).representation →
      BernsteinShiftedDerivativePositiveBelow T ψ
        ((T.binaryNormalizedProductFunctor a b).obj (A, B)) (r + s)

end Langlands.Classification
