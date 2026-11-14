# All-field port of `Langlands.Representation.GodementJacquet.ModelWhittakerRationalityProof`

`Langlands.AllField.Representation.GodementJacquet.ModelWhittakerRationalityProof` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.ModelWhittakerRationalityProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.ModelWhittakerRationalityProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Convergence and rationality of Whittaker matrix integrals on the model**

The conditional coefficient-model theorem is applied to the full Whittaker
torus asymptotic theorem and finite-function Mellin theorem. See the paired
Markdown for the implemented proof and its source provenance.

## Imports from the port

- `Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerModelRationality`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof`
- `Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof`

## Declarations

- `Langlands.AllField.GodementJacquet.modelWhittakerRationality` (theorem): Every shifted full-matrix Whittaker integral on the coefficient model
  converges on a right half-plane and has a rational continuation in `q^(-s)`.
