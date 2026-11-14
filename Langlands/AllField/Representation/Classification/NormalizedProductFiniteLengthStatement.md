# All-field port of `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`

`Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthStatement` is the all-field port of the Library module `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite length of normalized products of smooth GL factors**

Henniart (2002), §2.5, and the block-factor specialization of Casselman
(1 May 1995), Corollary 6.3.8. These are proposition definitions, not proofs.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockFactors`

## Declarations

- `Langlands.AllField.Classification.IrreducibleProductFiniteLength` (def): Normalized upper parabolic induction of a finite family of arbitrary
  irreducible smooth complex GL factors has finite group-module length.
  The block shape includes positivity of each rank and their sum.
- `Langlands.AllField.Classification.AdmissibleFiniteLengthProductPreservation` (def): Normalized upper parabolic product induction preserves finite length
  when every smooth complex block factor is admissible and of finite length.
  Admissibility alone is not the premise.

Public declarations of the original that are not re-declared here: `Langlands.Classification.PadicNormalizedProductFiniteLengthTheorems`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
