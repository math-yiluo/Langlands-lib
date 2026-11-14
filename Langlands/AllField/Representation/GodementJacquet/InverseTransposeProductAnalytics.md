# All-field port of `Langlands.Representation.GodementJacquet.InverseTransposeProductAnalytics`

`Langlands.AllField.Representation.GodementJacquet.InverseTransposeProductAnalytics` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.InverseTransposeProductAnalytics`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.InverseTransposeProductAnalytics` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Inverse-transpose analytics and the reversed ordered block family**

The published upper-to-opposite and opposite-to-reversed-upper transports are
composed as actual representation equivalences. Coefficient transport then
identifies the transformed analytic predicate with the ordinary predicate on
this reversed family, retaining the prescribed measure and polynomial.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.AnalyticData`
- `Langlands.AllField.Representation.Induction.InverseTranspose`
- `Langlands.AllField.Representation.Induction.OppositeProductReversalProof`

## Declarations

- `Langlands.AllField.GodementJacquet.inverseTransposeProductReversalEquiv` (def): The inverse-transpose pullback of the actual upper product induction is
  equivalent to the reversed upper product of the inverse-transpose factors.
  The reversal includes the entire dependent carrier family.
- `Langlands.AllField.GodementJacquet.iotaMatrixAnalyticAssertions_product_iff` (theorem): The transformed analytic assertions for the original actual product
  induction are exactly the ordinary assertions for the reversed upper product
  of the pulled-back factors. The polynomial and measure are unchanged.
