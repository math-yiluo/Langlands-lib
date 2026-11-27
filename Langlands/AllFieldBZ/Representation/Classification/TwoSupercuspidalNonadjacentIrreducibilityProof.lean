import Langlands.AllFieldBZ.Representation.Classification.NonadjacentLeibnizPieces
import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof

/-!
# All-field port of `Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`

Zelevinsky 1980, Proposition 1.11(a), first conjunct: the upper normalized product of
two supercuspidal representations is irreducible unless one is the `ν = |det|` twist of
the other. The proof is the Bernstein–Zelevinsky derivative argument assembled in
`NonadjacentAssembly`, with every derivative input discharged by its proof in the Library.

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

namespace Langlands.AllFieldBZ.Classification

universe uF uV

/-- Ze80 Proposition 1.11(a), first conjunct: nonadjacent two-supercuspidal products are
irreducible. -/
theorem twoSupercuspidalNonadjacentProductIrreducible
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  NonadjacentAssembly.nonadjacent_of_leibnizFiltration F T
    (Langlands.AllFieldBZ.Derivative.generalLinearDerivativeLeibnizFiltration.{uF, uV} F T)

end Langlands.AllFieldBZ.Classification
