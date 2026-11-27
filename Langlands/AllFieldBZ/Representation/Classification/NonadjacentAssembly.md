# All-field port of `Langlands.Representation.Classification.NonadjacentAssembly`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.NonadjacentAssembly`. Original module: `Langlands.Representation.Classification.NonadjacentAssembly`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/NonadjacentAssembly.md`.

## Content

The core of the BZ77 Theorem 4.2 argument: if the top derivative of `π` on `GL_(N+1)` is one-dimensional and, at every intermediate order, the derivatives of `π` and of `ν π~` have filtrations whose graded pieces are zero or irreducible and pairwise carry no invariant forms, then `π` is irreducible (`irreducible_of_pieces`). Exactness of derivatives, detection by derivatives and BZ77 Proposition 3.8 enter as hypotheses, in their all-field forms `Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeExactnessStatement`, `Langlands.AllFieldBZ.Derivative.MirabolicDerivativeDetection` and `Langlands.AllFieldBZ.Derivative.MirabolicHighestDerivativePairingStatement`.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.NonadjacentAssembly.dualTwistRep` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.dualTwistRep` |
| `Langlands.Classification.NonadjacentAssembly.restrictedDerivative` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.restrictedDerivative` |
| `Langlands.Classification.NonadjacentAssembly.restrictedDerivative_exact` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.restrictedDerivative_exact` |
| `Langlands.Classification.NonadjacentAssembly.PiecesWithoutForms` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.PiecesWithoutForms` |
| `Langlands.Classification.NonadjacentAssembly.false_of_constituent` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.false_of_constituent` |
| `Langlands.Classification.NonadjacentAssembly.irreducible_of_pieces` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.irreducible_of_pieces` |

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

The field-independent declarations `Langlands.Classification.NonadjacentAssembly.isSubOrQuotient_map` and `formsCast` are used unchanged.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
