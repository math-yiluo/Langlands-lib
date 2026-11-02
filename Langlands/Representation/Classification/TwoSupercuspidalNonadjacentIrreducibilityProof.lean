import Langlands.Representation.Classification.NonadjacentLeibnizPieces
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof

/-!
# Irreducibility of nonadjacent two-supercuspidal products

Zelevinsky 1980, Proposition 1.11(a), first conjunct: the upper normalized product of
two supercuspidal representations is irreducible unless one is the `ν = |det|` twist of
the other. The proof is the Bernstein–Zelevinsky derivative argument assembled in
`NonadjacentAssembly`, with every derivative input discharged by its published proof.
-/

namespace Langlands.Classification

universe uF uV

/-- Ze80 Proposition 1.11(a), first conjunct: nonadjacent two-supercuspidal products are
irreducible. -/
theorem twoSupercuspidalNonadjacentProductIrreducible
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  NonadjacentAssembly.nonadjacent_of_leibnizFiltration F T
    (Derivative.generalLinearDerivativeLeibnizFiltration.{uF, uV} F T)

end Langlands.Classification
