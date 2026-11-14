# All-field port of `Langlands.Group.GL.LowerTriangularQuotientCell`

`Langlands.AllField.Group.GL.LowerTriangularQuotientCell` is the all-field port of the Library module `Langlands.Group.GL.LowerTriangularQuotientCell`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.LowerTriangularQuotientCell` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The open lower-triangular cell of the left-unipotent quotient**

The coset map `B⁻_m → N_m \ GL_m`, `b ↦ [b]`, is an open embedding. Injectivity
is `N_m ∩ B⁻_m = 1`; openness comes from the singleton-shape Iwahori
factorization, which places every small compact open subgroup `K` inside
`N_m · (K ∩ B⁻_m)`.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Group.GL.CompactOpenSupplement`

## Declarations

- `Langlands.AllField.GeneralLinear.exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular` (theorem): Arbitrarily small compact open subgroups `K` satisfy `K ⊆ N_m · (K ∩ B⁻_m)`.
- `Langlands.AllField.GeneralLinear.isOpen_upperUnipotent_mul_lowerTriangular_inter` (theorem): For every open set `O`, the set `N_m · (B⁻_m ∩ O)` is open.
- `Langlands.AllField.GeneralLinear.isOpenEmbedding_lowerTriangularQuotientMap` (theorem): The coset map `B⁻_m → N_m \ GL_m` is an open embedding.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.eq_one_of_mem_upperUnipotent_of_mem_lowerTriangular`, `Langlands.GeneralLinear.singletons_oppositeUnipotentSubgroup_le_lowerTriangular`, `Langlands.GeneralLinear.singletons_leviSubgroup_le_lowerTriangular`, `Langlands.GeneralLinear.lowerTriangularQuotientMap`, `Langlands.GeneralLinear.lowerTriangularQuotientMap_apply`, `Langlands.GeneralLinear.lowerTriangularQuotientMap_injective`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
