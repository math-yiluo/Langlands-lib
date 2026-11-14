# All-field port of `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`

`Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

BZ77 2.8: proof that the total count of minimal conjugating block
permutations is the factorial of the source block count.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountStatement`
- `Langlands.AllField.Representation.Geometric.WeylStatementSupplement`

## Declarations

- `Langlands.AllField.CuspidalSupport.totalConjugatingCount` (theorem): BZ77 2.8, `l(M) = r!`: over every finite p-adic extension and every rank,
  the minimal permutations conjugating a standard Levi onto some standard Levi
  are counted, over all target shapes, by the factorial of the block count.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.TotalConjugatingCount.index_surjective`, `Langlands.CuspidalSupport.TotalConjugatingCount.card_blockIndex_fiber`, `Langlands.CuspidalSupport.TotalConjugatingCount.shape_ext`, `Langlands.CuspidalSupport.TotalConjugatingCount.mem_map_conj_iff`, `Langlands.CuspidalSupport.TotalConjugatingCount.swap_entries_vanish_iff`, `Langlands.CuspidalSupport.TotalConjugatingCount.conjugatesLevi_iff`, `Langlands.CuspidalSupport.TotalConjugatingCount.blockIndex_apply`, `Langlands.CuspidalSupport.TotalConjugatingCount.blockMap_injective`, `Langlands.CuspidalSupport.TotalConjugatingCount.blockMap_surjective`, `Langlands.CuspidalSupport.TotalConjugatingCount.blockMap_bijective`, `Langlands.CuspidalSupport.TotalConjugatingCount.length_eq`, `Langlands.CuspidalSupport.TotalConjugatingCount.size_blockMap`, `Langlands.CuspidalSupport.TotalConjugatingCount.range_block`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderedShape`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderIndex`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderPerm`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderPerm_index`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderPerm_symm_index`, `Langlands.CuspidalSupport.TotalConjugatingCount.blockIndex_reorderPerm`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderPerm_minimal`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderPerm_conjugates`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderElement`, `Langlands.CuspidalSupport.TotalConjugatingCount.blockValue`, `Langlands.CuspidalSupport.TotalConjugatingCount.blockValue_reorderElement`, `Langlands.CuspidalSupport.TotalConjugatingCount.eq_of_blockValue_eq`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderElement_injective`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderElement_surjective`, `Langlands.CuspidalSupport.TotalConjugatingCount.reorderElement_bijective`, `Langlands.CuspidalSupport.TotalConjugatingCount.finite_and_card_eq`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
