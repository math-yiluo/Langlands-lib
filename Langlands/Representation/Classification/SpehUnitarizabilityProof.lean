import Langlands.Representation.Classification.SpehUnitarizabilityReductionProof
import Langlands.Representation.Classification.TadicComplementarySeriesProof
import Langlands.Representation.Classification.BernsteinUnitaryProductIrreducibilityProof
import Langlands.Representation.Classification.BernsteinUnitaryFactorProof
import Langlands.Representation.Classification.SpehComplementaryIrreducibilityProof
import Langlands.Representation.Classification.SpehNeighborProductIrreducibilityProof
import Langlands.Representation.Classification.SpehNeighborProductEndpointProof

/-!
# Unitarizability of Speh representations

Tadic 1986, Appendix, Theorem A.8: every Speh representation `u(delta, k)` of
`GL_(k r)` over a p-adic field is unitarizable. The proof composes Tadic's local
reduction `spehUnitarizabilityLocalReduction` (Tadic 1986, Lemma 6.2; Badulescu 2014,
Theorem 1(b)) with the published proofs of all six of its hypotheses.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Tadic 1986, Theorem A.8.** For every discrete-series datum `d = (delta, k)`,
every actual smooth representation `π` of `GL_(k r)` with `d.IsSpeh π`, that is,
every representative of the Speh representation `u(delta, k)`, is unitarizable. -/
theorem spehUnitarizability : SpehUnitarizability.{uF, uV} F T :=
  spehUnitarizabilityLocalReduction.{uF, uV} F T
    (complementarySeriesUnitarity.{uF, uV} F T)
    (bernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (bernsteinUnitaryProductFactorUnitarity.{uF, uV} F T)
    ⟨spehComplementaryIrreducibility.{uF, uV} F T,
      spehNeighborProductIrreducibility.{uF, uV} F T,
      spehNeighborProductEndpointSubquotient.{uF, uV}⟩

end Langlands.Classification
