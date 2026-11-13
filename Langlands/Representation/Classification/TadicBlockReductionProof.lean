import Langlands.Representation.Classification.TadicBlockReductionAssembly
import Langlands.Representation.Classification.BernsteinUnitaryProductIrreducibilityProof
import Langlands.Representation.Classification.BernsteinShiftedHighestDerivativeUnitarityProof
import Langlands.Representation.Classification.TadicComplementarySeriesUnitarityProof
import Langlands.Representation.Classification.UnlinkedSocleProductIrreducibilityProof
import Langlands.Representation.Classification.TadicRectangleSoclePrimeProof
import Langlands.Representation.Classification.UnitarizableSocleHermitianSymmetryProof

/-! Proof of `TadicBlockReduction` (Tadić 1986, Lemma 4.8(ii), existence of the
factorization into members of `X_m` under `(U^m)`). -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Tadić 1986, Lemma 4.8(ii)** (existence): under `(U^m)`, every irreducible unitarizable
representation of `GL_(m+1)` that is not a Zelevinsky socle `⟨a(n,d)^ρ⟩` with `ρ` unitary
is the normalized product of members of `X_m`. -/
theorem tadicBlockReduction : TadicBlockReduction.{uF, uV} F T :=
  TadicBlockReductionAssembly.tadicBlockReduction_of_inputs F T
    (bernsteinUnitaryProductIrreducibility F T)
    (bernsteinShiftedHighestDerivativeUnitarity F T)
    (complementarySeriesOpenIntervalUnitarity F T)
    (unlinkedSocleProductIrreducibility F T)
    (TadicRectanglePrime.tadicRectangleSoclePrime F T)
    (unitarizableSocleHermitianSymmetry F T)

end Langlands.Classification
