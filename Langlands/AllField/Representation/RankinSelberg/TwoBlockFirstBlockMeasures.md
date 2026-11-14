# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockMeasures` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Restriction-normalized measures for the first-block quotient**

The Haar measure on the norm-one first block is pulled back from the ambient
general linear Haar measure through the open subgroup inclusion. The mixed
subgroup has the transported product Haar measure.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentMeasures`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.isOpenEmbedding_normOneSubtype` (theorem): The norm-one subgroup inclusion is an open embedding.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneHaar` (def): Haar measure on `GL_(n+1)^0`, normalized by restriction from `GL_(n+1)`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneHaar_isHaar` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneHaar_regular` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneHaar_isMulRightInvariant` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.map_normOneHaar` (theorem): The normalization is an exact equality of measures.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedHaar` (def): Product Haar measure on the actual mixed subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedHaar_isHaar` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedHaar_regular` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedHaar_isMulRightInvariant` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixed_compatibleMeasureExists` (theorem): Compatible quotient existence for the fixed restriction-normalized pair.
