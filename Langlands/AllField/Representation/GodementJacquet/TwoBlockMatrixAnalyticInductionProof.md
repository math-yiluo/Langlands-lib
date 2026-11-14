# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionProof`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionProof` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conditional two-block Godement–Jacquet analytic induction**

The ordinary two-block analytic induction follows from the actual generator
inputs (forward finite product expansions and reverse realization) for the
canonical normalized induced representation; the reduction module then gives the
published conditional statement, including the transformed predicate.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.TwoBlockAnalyticReduction`
- `Langlands.AllField.Representation.GodementJacquet.TwoBlockReverseRealization`

## Declarations

- `Langlands.AllField.GodementJacquet.twoBlockOrdinaryMatrixAnalyticInduction` (theorem): Ordinary two-block analytic induction for the canonical normalized induced
  representation of two smooth admissible blocks.
- `Langlands.AllField.GodementJacquet.twoBlockMatrixAnalyticInduction` (theorem): **Conditional two-block Godement–Jacquet analytic induction.**
