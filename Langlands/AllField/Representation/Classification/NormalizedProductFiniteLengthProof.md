# All-field port of `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof`

`Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthProof` is the all-field port of the Library module `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Finite-length preservation for actual normalized induction.

## Imports from the port

- `Langlands.AllField.Representation.Classification.IrreducibleProductFiniteLengthProof`
- `Langlands.AllField.Representation.Parabolic.InductionExactnessProof`
- `Langlands.AllField.Representation.Tensor.FactorMatchingProof`

## Declarations

- `Langlands.AllField.Classification.ProductLengthProof.irreducibleLevi` (theorem).
- `Langlands.AllField.Classification.ProductLengthProof.step` (theorem).
- `Langlands.AllField.Classification.ProductLengthProof.leviPreservation` (theorem).
- `Langlands.AllField.Classification.normalizedInductionFiniteLength` (theorem): Normalized induction of an arbitrary admissible finite-length standard-Levi
  representation has finite group-algebra length at positive total rank.
- `Langlands.AllField.Classification.admissibleFiniteLengthProductPreservation` (theorem): The complete admissible finite-length block-product preservation statement.

Public declarations of the original that are not re-declared here: `Langlands.Classification.ProductLengthProof.finiteLength_of_range_eq_ker`, `Langlands.Classification.ProductLengthProof.finiteLength_of_injective`, `Langlands.Classification.ProductLengthProof.finiteLength_of_surjective`, `Langlands.Classification.ProductLengthProof.selfMatching_of_finiteLength`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
