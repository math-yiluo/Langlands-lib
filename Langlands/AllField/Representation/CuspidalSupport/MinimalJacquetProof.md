# All-field port of `Langlands.Representation.CuspidalSupport.MinimalJacquetProof`

`Langlands.AllField.Representation.CuspidalSupport.MinimalJacquetProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.MinimalJacquetProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.MinimalJacquetProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Nonzero quasicuspidal Jacquet descent**

A proof of `MinimalNonzeroJacquetTheorem` (BZ77 section 2.14(1)). A block shape
with at most one block has trivial radical, so the Jacquet module of a nonzero
representation along it is nonzero. Among the shapes with nonzero normalized
Jacquet module, take one with the largest number of blocks. If a proper
refinement of it had nonzero inner coinvariants, the flattened shape would have
more blocks and, through a surjection onto those coinvariants, a nonzero Jacquet
module.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.MinimalJacquetStatement`
- `Langlands.AllField.Representation.Parabolic.RefinementComposition`

## Declarations

- `Langlands.AllField.CuspidalSupport.MinimalJacquet.mk_jacquetMk_composedUnipotent` (theorem): An element of the composite radical acts trivially on the inner coinvariants of
  the outer normalized Jacquet module, since the outer half-modulus is trivial on the
  inner radical.
- `Langlands.AllField.CuspidalSupport.MinimalJacquet.flattenJacquetMap` (def): The flattened Jacquet module maps onto the inner coinvariants of the outer
  normalized Jacquet module.
- `Langlands.AllField.CuspidalSupport.MinimalJacquet.flattenJacquetMap_surjective` (theorem).
- `Langlands.AllField.CuspidalSupport.MinimalJacquet.nontrivial_flatten` (theorem): Nonzero inner coinvariants give a nonzero flattened Jacquet module.
- `Langlands.AllField.CuspidalSupport.minimalNonzeroJacquet` (theorem): Nonzero quasicuspidal Jacquet descent for every rank, including rank zero.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_of`, `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_iff`, `Langlands.GeneralLinear.BlockShape.index_lt_iff`, `Langlands.GeneralLinear.BlockShape.flatten`, `Langlands.GeneralLinear.BlockShape.flattenBlockEquiv`, `Langlands.GeneralLinear.BlockShape.flattenBlockEquiv_lt_iff`, `Langlands.GeneralLinear.BlockShape.flatten_size_flattenBlockEquiv`, `Langlands.GeneralLinear.BlockShape.index_index_lt`, `Langlands.GeneralLinear.BlockShape.flatten_index`, `Langlands.GeneralLinear.BlockShape.index_index_eq_flatten`, `Langlands.GeneralLinear.BlockShape.one_le_refinement_length`, `Langlands.GeneralLinear.BlockShape.length_lt_flatten`, `Langlands.GeneralLinear.BlockShape.flatten_unipotentSubgroup_le`, `Langlands.GeneralLinear.BlockShape.exists_length_le_one`, `Langlands.GeneralLinear.BlockShape.unipotentRadical_val_eq_one`, `Langlands.GeneralLinear.BlockShape.jacquetMk_injective_of_length_le_one`, `Langlands.GeneralLinear.BlockShape.nontrivial_jacquetModule_of_length_le_one`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
