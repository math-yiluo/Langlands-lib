# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockAnalyticReversal`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockAnalyticReversal` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockAnalyticReversal`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockAnalyticReversal` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Canonical analytic inputs for the reversed inverse-transpose block family**

These adapters identify the actual reversed family in the published matrix
analytic predicate, and transport its admissibility and scalar central action.
They do not supply the noncompact analytic-induction argument.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.InverseTransposeProductAnalytics`
- `Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.matrixAnalyticAssertions_reversedInverseTransposeBlocks` (theorem): Each block's actual transformed analytic assertion is precisely the
  ordinary assertion for the corresponding reversed pullback block.
- `Langlands.AllField.GodementJacquet.Padic.iotaMatrixAnalyticAssertions_succBlocks_iff` (theorem): With canonical topology and Haar measure, the transformed assertion for
  upper normalized induction is the ordinary assertion for upper normalized
  induction of the complete reversed inverse-transpose block family. This
  includes the reindexing of the proposed polynomial factors.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.inverseTranspose_scalar`, `Langlands.Classification.hasGLCentralCharacter_comp_inverseTranspose`, `Langlands.GodementJacquet.reversedInverseTransposeBlocks`, `Langlands.GodementJacquet.sum_reversedSuccBlocks`, `Langlands.GodementJacquet.isAdmissible_reversedInverseTransposeBlocks`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
