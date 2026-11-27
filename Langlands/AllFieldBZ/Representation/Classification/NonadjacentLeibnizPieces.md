# All-field port of `Langlands.Representation.Classification.NonadjacentLeibnizPieces`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.NonadjacentLeibnizPieces`. Original module: `Langlands.Representation.Classification.NonadjacentLeibnizPieces`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/NonadjacentLeibnizPieces.md`.

## Content

`TwoBlockDerivativePieces` from the Leibniz filtration (BZ77 4.14(c)) and the derivatives of supercuspidal representations (BZ77 4.4), and the chain of theorems `nonadjacent_of_leibniz`, `nonadjacent_of_exactness_leibniz`, `nonadjacent_of_exactness_leibnizFiltration` and `nonadjacent_of_leibnizFiltration` which discharge exactness, detection, BZ77 3.8 and BZ77 4.4 with their all-field proofs (`Langlands.AllFieldBZ.Derivative.generalLinearDerivativeExactness`, `Langlands.AllFieldBZ.Derivative.Mirabolic.derivativeDetection`, `Langlands.AllFieldBZ.Derivative.mirabolicHighestDerivativePairing`, `Langlands.AllFieldBZ.Classification.supercuspidalDerivatives`).

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.NonadjacentAssembly.SupercuspidalDerivativePattern` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.SupercuspidalDerivativePattern` |
| `Langlands.Classification.NonadjacentAssembly.supercuspidalDerivativePattern` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.supercuspidalDerivativePattern` |
| `Langlands.Classification.NonadjacentAssembly.leibnizPiece_cases` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.leibnizPiece_cases` |
| `Langlands.Classification.NonadjacentAssembly.finrank_leibnizPiece_top` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.finrank_leibnizPiece_top` |
| `Langlands.Classification.NonadjacentAssembly.finrank_top_binary` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.finrank_top_binary` |
| `Langlands.Classification.NonadjacentAssembly.exists_filtration_binary` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.exists_filtration_binary` |
| `Langlands.Classification.NonadjacentAssembly.restrictedDerivative_twoBlockProduct` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.restrictedDerivative_twoBlockProduct` |
| `Langlands.Classification.NonadjacentAssembly.twoBlockDerivativePieces_of_leibniz` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.twoBlockDerivativePieces_of_leibniz` |
| `Langlands.Classification.NonadjacentAssembly.nonadjacent_of_leibniz` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.nonadjacent_of_leibniz` |
| `Langlands.Classification.NonadjacentAssembly.nonadjacent_of_exactness_leibniz` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.nonadjacent_of_exactness_leibniz` |
| `Langlands.Classification.NonadjacentAssembly.nonadjacent_of_exactness_leibnizFiltration` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.nonadjacent_of_exactness_leibnizFiltration` |
| `Langlands.Classification.NonadjacentAssembly.nonadjacent_of_leibnizFiltration` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.nonadjacent_of_leibnizFiltration` |

## Systematic changes

- `Langlands.PadicField.{u} p` becomes `Langlands.AllFieldBZ.LocalFieldPackage.{u}`; the prime
  `p` and its `Fact p.Prime` instance are removed from binders and quantifiers, and the
  corresponding explicit arguments are dropped.
- Normalization API names on `T` (for example `Integers`, `ord`, `normalizedAbs`, `uniformizer`)
  resolve to `Langlands.LocalFieldData`.
- Every ported declaration `Langlands.X` is renamed `Langlands.AllFieldBZ.X` (with
  `PadicField.TopologicalData` replaced by `LocalFieldPackage.TopologicalData`). References to
  declarations that already have all-field versions in the Library use those versions (for
  example `Langlands.AllFieldBZ.Derivative.generalLinearDerivative` for
  `Langlands.Derivative.generalLinearDerivative`, and the `_allFieldBZ` versions of the
  `Langlands.GeneralLinear` declarations such as `compactOpen_cofinal`).
- References to field-independent declarations of the original module and of other p-adic
  modules are written with their full original names, so those declarations are used unchanged.
  Private field-independent helpers, which cannot be referenced from another module, are
  repeated as private declarations.

## Changes beyond the systematic replacements

The field-independent lemmas `Langlands.Classification.NonadjacentAssembly.nonempty_linearEquiv_graded_of_length_one` and `card_leibnizIndices_top` are used unchanged.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
