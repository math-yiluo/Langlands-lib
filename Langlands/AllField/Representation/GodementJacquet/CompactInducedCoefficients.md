# All-field port of `Langlands.Representation.GodementJacquet.CompactInducedCoefficients`

`Langlands.AllField.Representation.GodementJacquet.CompactInducedCoefficients` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.CompactInducedCoefficients`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.CompactInducedCoefficients` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The actual compact integral formula for normalized induced coefficients**

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.GodementJacquet.Zeta`
- `Langlands.AllField.Representation.Induction.CompactScalarProof`
- `Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof`
- `Langlands.AllField.Representation.Parabolic.NormalizedInductionStatementSupplement`
- `Langlands.AllField.Representation.Parabolic.RefinedInductionAdmissibility`
- `Langlands.AllField.Representation.Parabolic.RefinedInductionTensorNormalization`

## Declarations

- `Langlands.AllField.GodementJacquet.compactInducedCoefficientKernel` (def): The scalar compact-picture integrand, with the first induced section in the
  induction of the smooth dual and the second section translated on the right.
- `Langlands.AllField.GodementJacquet.exists_compactInducedCoefficientFormula` (theorem): In every positive rank there is one compact open Iwasawa subgroup with a
  Haar probability measure for which every smooth functional on an admissible
  normalized induction has the actual compact coefficient formula.
