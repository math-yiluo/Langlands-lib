# All-field port of `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof`

`Langlands.AllField.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Square-summability of square-integrable Whittaker functions on the torus lattice**

The proof compares Whittaker functions with matrix coefficients. By the simple-root support
bound, a Whittaker function vanishes at `ϖ^μ` unless `μ` lies in a translate of the antitone
cone. On the antitone cone, a Whittaker function agrees with a smooth `K(r)`-invariant
matrix coefficient, and square-integrability modulo the centre makes these values
square-summable against the inverse modulus.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`
- `Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar`
- `Langlands.AllField.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof`
- `Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof`

## Declarations

- `Langlands.AllField.RankinSelberg.SquareIntegrableWhittakerTorusSum.normalizedAbs_zpow` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.torusModulus`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.torusModulus_add`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.torusModulus_pos`, `Langlands.RankinSelberg.squareIntegrableWhittakerTorusSum`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
