# All-field supplement to `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`

`Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement` supplements the Library module `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`, the existing all-field port of `Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

BZ77 cuspidal embedding, finite length, association, and Hom bounds.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`

## Declarations

- `Langlands.AllField.CuspidalSupport.CuspidalInductionLengthTheorem` (def): Irreducible cuspidal induction has finite group-module length and an
  actual composition series with at most the factorial of the block count
  many factors.

Declarations of the original re-declared by `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement` and therefore not here: `Langlands.CuspidalSupport.CuspidalEmbeddingTheorem`.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.CuspidalInductionAssociationTheorem`, `Langlands.CuspidalSupport.CuspidalInductionHomBoundTheorem`, `Langlands.CuspidalSupport.PadicCuspidalInductionTheorems`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
