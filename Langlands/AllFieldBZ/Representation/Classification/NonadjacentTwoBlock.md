# All-field port of `Langlands.Representation.Classification.NonadjacentTwoBlock`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.NonadjacentTwoBlock`. Original module: `Langlands.Representation.Classification.NonadjacentTwoBlock`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/NonadjacentTwoBlock.md`.

## Content

The BZ77 Theorem 4.2 core applied to the two-block product `ρ × ρ'` of supercuspidal representations: the intermediate proposition `TwoBlockDerivativePieces` (a consequence of the Leibniz rule and of the derivatives of supercuspidal representations), the pieces built from supercuspidal classes, and `nonadjacent_of_twoBlockDerivativePieces`, which derives Zelevinsky 1980, Proposition 1.11(a) from exactness, detection, BZ77 3.8 and `TwoBlockDerivativePieces`.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.NonadjacentAssembly.PieceIn` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.PieceIn` |
| `Langlands.Classification.NonadjacentAssembly.length_eq_zero_of_pieceIn` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.length_eq_zero_of_pieceIn` |
| `Langlands.Classification.NonadjacentAssembly.twoBlockProduct` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.twoBlockProduct` |
| `Langlands.Classification.NonadjacentAssembly.twoBlockProductRaw` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.twoBlockProductRaw` |
| `Langlands.Classification.NonadjacentAssembly.TwoBlockDerivativePieces` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.TwoBlockDerivativePieces` |
| `Langlands.Classification.NonadjacentAssembly.isIrreducible_rankCast` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.isIrreducible_rankCast` |
| `Langlands.Classification.NonadjacentAssembly.zeroOrIrreducible_of_pieceIn` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.zeroOrIrreducible_of_pieceIn` |
| `Langlands.Classification.NonadjacentAssembly.pieceIn_of_equiv` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.pieceIn_of_equiv` |
| `Langlands.Classification.NonadjacentAssembly.pieceIn_of_twoBlock` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.pieceIn_of_twoBlock` |
| `Langlands.Classification.NonadjacentAssembly.twoBlockDualTwistSucc` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.twoBlockDualTwistSucc` |
| `Langlands.Classification.NonadjacentAssembly.twoBlockDualTwistIso` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.twoBlockDualTwistIso` |
| `Langlands.Classification.NonadjacentAssembly.piecesWithoutForms_twoBlock` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.piecesWithoutForms_twoBlock` |
| `Langlands.Classification.NonadjacentAssembly.nonadjacent_of_twoBlockDerivativePieces` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.nonadjacent_of_twoBlockDerivativePieces` |

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

The field-independent shape `Langlands.Classification.NonadjacentAssembly.twoBlocksSucc` is used unchanged. The nontrivial unitary additive character needed for the derivatives is obtained from `Langlands.HarmonicAnalysis.nonempty_unitaryAdditiveCharacter`, which holds for every nonarchimedean local field, in place of the p-adic existence theorem.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
