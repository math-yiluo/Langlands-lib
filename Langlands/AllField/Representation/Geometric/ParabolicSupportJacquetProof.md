# All-field port of `Langlands.Representation.Geometric.ParabolicSupportJacquetProof`

`Langlands.AllField.Representation.Geometric.ParabolicSupportJacquetProof` is the all-field port of the Library module `Langlands.Representation.Geometric.ParabolicSupportJacquetProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Geometric.ParabolicSupportJacquetProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The natural image and successive-quotient comparison for normalized coinvariants.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.ParabolicSupportJacquetStatement`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetExactnessProof`

## Declarations

- `Langlands.AllField.Geometric.supportCoinvariantsImageHom_injective` (theorem).
- `Langlands.AllField.Geometric.supportCoinvariantsImageIso` (def): Exactness identifies the support coinvariants with their actual ambient image.
- `Langlands.AllField.Geometric.supportImageNatIso` (def): The stepwise coinvariant-to-image comparison is natural in the source representation.
- `Langlands.AllField.Geometric.supportImageToQuotient` (def): Project the actual upper image to the coinvariants of the support quotient.
- `Langlands.AllField.Geometric.supportImageToQuotient_on_support` (theorem).
- `Langlands.AllField.Geometric.supportImageToQuotient_ker` (theorem): The projection out of the image has precisely the lower image as kernel.
- `Langlands.AllField.Geometric.supportImageToQuotient_surjective` (theorem): Surjectivity follows from the actual quotient map and the upper-image isomorphism.
- `Langlands.AllField.Geometric.supportImageQuotientHom` (def): Descend the projection to the actual quotient of the two Jacquet images.
- `Langlands.AllField.Geometric.supportImageQuotientHom_bijective` (theorem).
- `Langlands.AllField.Geometric.supportImageQuotientIso` (def): Exactness gives a natural isomorphism of successive support-image quotients.
- `Langlands.AllField.Geometric.padicParabolicSupportJacquetComparison` (theorem): The exact natural comparison for the published fixed support filtration.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.supportInclusion`, `Langlands.Geometric.supportCoinvariantsMap`, `Langlands.Geometric.supportCoinvariantsMap_mk`, `Langlands.Geometric.supportCoinvariantsImageHom`, `Langlands.Geometric.supportCoinvariantsImageHom_mk`, `Langlands.Geometric.supportCoinvariantsImageHom_surjective`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
