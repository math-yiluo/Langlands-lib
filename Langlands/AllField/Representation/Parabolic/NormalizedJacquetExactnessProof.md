# All-field port of `Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof`

`Langlands.AllField.Representation.Parabolic.NormalizedJacquetExactnessProof` is the all-field port of the Library module `Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Exactness of the actual normalized block Jacquet maps**

The radical quotient is Mathlib's coinvariant quotient for the actual block
unipotent radical, and the normalizing twist and Levi action leave the
underlying linear maps unchanged.  Exactness therefore reduces to the generic
smooth coinvariant exactness of `Langlands.Representation.Jacquet.ExactProof`,
whose finite-containment hypothesis is the published
`unipotentFiniteContainment` for the actual radical.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Representation.Geometric.RefinementDefinitionsSupplement`
- `Langlands.AllField.Representation.Jacquet.ParabolicSupplement`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement`
- `Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment`

## Declarations

- `Langlands.AllField.Parabolic.isSmooth_radical` (theorem): A smooth ambient action stays smooth on the actual block radical.
- `Langlands.AllField.Parabolic.radicalCoinvariants_exact` (theorem): Exactness of the unnormalized radical quotient maps, stated on Mathlib's
  coinvariant maps for the actual block unipotent radical. Only the middle term
  needs to be smooth.
- `Langlands.AllField.Parabolic.normalizedJacquetExactness` (theorem): The actual normalized block Jacquet maps are exact on short exact
  sequences of smooth complex representations.
- `Langlands.LocalFieldData.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap` (theorem): Both are Mathlib's coinvariant map for the actual block unipotent radical.
- `Langlands.LocalFieldData.normalizedJacquetMap_exact` (theorem): Exactness of the actual normalized Jacquet maps, obtained from
  `Langlands.AllField.Parabolic.normalizedJacquetExactness`. The outer terms are smooth because they
  are a subrepresentation and a quotient of the smooth middle term.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.normalizedJacquetMap_toLinearMap`, `Langlands.PadicField.TopologicalData.normalizedJacquetFunctor_map_hom`, `Langlands.PadicField.TopologicalData.normalizedJacquetFunctor_map_exact`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
