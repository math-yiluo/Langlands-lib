import Langlands.Representation.Classification.BernsteinUnitaryRankInduction
import Langlands.Representation.Classification.BernsteinShiftedHighestDerivativeUnitarityProof
import Langlands.Representation.Classification.BernsteinLowerDerivativePositivityProof
import Langlands.Representation.Classification.BernsteinProductPositivityProof
import Langlands.Representation.Classification.BernsteinUnitaryIrreducibilityCriterionProof

/-! Bernstein's irreducibility theorem for finite normalized products of
irreducible unitarizable representations, from the proved analytic inputs. -/

noncomputable section

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- All four analytic inputs of Bernstein's binary rank induction hold. -/
theorem bernsteinUnitaryInductionInputs :
    BernsteinUnitaryInductionInputs.{uF, uV} F T :=
  ⟨bernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T,
    bernsteinUnitaryLowerDerivativePositivity.{uF, uV} F T,
    bernsteinUnitaryTopDerivativeProductPositivity.{uF, uV} F T,
    bernsteinUnitaryFiniteLengthIrreducibilityCriterion.{uF, uV} F T⟩

/-- Bernstein 1984, Corollary 8.2(a), and Tadic 1986, Theorem 2.5(i):
every finite normalized product of irreducible unitarizable blocks is
irreducible and unitarizable. -/
theorem bernsteinUnitaryProductIrreducibility :
    BernsteinUnitaryProductIrreducibility.{uF, uV} F T :=
  bernsteinUnitaryProductIrreducibility_of_inductionInputs F T
    (bernsteinUnitaryInductionInputs.{uF, uV} F T)

end Langlands.Classification
