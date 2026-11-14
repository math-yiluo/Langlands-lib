# All-field port of `Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers`

`Langlands.AllField.Representation.CuspidalSupport.JacquetVanishingHelpers` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`

## Declarations

- `Langlands.AllField.CuspidalSupport.nonassociatedJacquetSubquotients_rankZero` (theorem): The nonassociation hypothesis is impossible at rank zero.
- `Langlands.AllField.CuspidalSupport.normalizedRefinedInductionFunctor_subsingleton` (theorem): Normalized refined induction of a zero representation is zero.
- `Langlands.AllField.CuspidalSupport.geometricPieceFunctor_subsingleton_of_proper_source` (theorem): A geometric piece vanishes when its source refinement is proper and
  its inducing representation is quasicuspidal.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.levisAssociated_rankZero`, `Langlands.CuspidalSupport.blockShape_rankZero_index_false`, `Langlands.CuspidalSupport.exists_associated_refinement_rankZero`, `Langlands.CuspidalSupport.quasicuspidalJacquetVanishing_rankZero`, `Langlands.CuspidalSupport.subgroupEqualityFunctor_subsingleton`, `Langlands.CuspidalSupport.subsingleton_of_isSubquotient`, `Langlands.CuspidalSupport.objectFiltrationAt`, `Langlands.CuspidalSupport.objectFiltrationAt_graded`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
