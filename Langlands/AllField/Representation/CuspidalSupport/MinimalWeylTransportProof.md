# All-field port of `Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof`

`Langlands.AllField.Representation.CuspidalSupport.MinimalWeylTransportProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Quasicuspidality of whole-Levi transport along a minimal conjugating permutation.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.WeylStatementSupplement`

## Declarations

- `Langlands.AllField.CuspidalSupport.minimalWeylTransportQuasicuspidal` (theorem): The published transport-quasicuspidality component, for every rank
  including zero.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.swap_mem_blockWeyl_iff`, `Langlands.CuspidalSupport.blockIndex_eq_iff_of_conjugatesLevi`, `Langlands.CuspidalSupport.blockIndex_apply_eq_blockMap`, `Langlands.CuspidalSupport.blockMap_bijective`, `Langlands.CuspidalSupport.blockEquiv`, `Langlands.CuspidalSupport.exists_index_eq_apply_index`, `Langlands.CuspidalSupport.innerMap`, `Langlands.CuspidalSupport.index_innerMap`, `Langlands.CuspidalSupport.innerMap_bijective`, `Langlands.CuspidalSupport.size_blockMap`, `Langlands.CuspidalSupport.apply_index_eq`, `Langlands.CuspidalSupport.leviConjugation_symm_block_entry`, `Langlands.CuspidalSupport.castShape`, `Langlands.CuspidalSupport.mem_castShape_parabolic_iff`, `Langlands.CuspidalSupport.mem_castShape_unipotentSubgroup_iff`, `Langlands.CuspidalSupport.pullbackRefinement`, `Langlands.CuspidalSupport.mem_refinedParabolic_pullback_iff`, `Langlands.CuspidalSupport.mem_refinedUnipotent_pullback_iff`, `Langlands.CuspidalSupport.refinedUnipotent_map_leviConjugation_symm`, `Langlands.CuspidalSupport.refinedParabolic_pullback_ne_top`, `Langlands.CuspidalSupport.isLeviQuasicuspidal_transport_of_refinement_images`, `Langlands.CuspidalSupport.isLeviQuasicuspidal_transport`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
