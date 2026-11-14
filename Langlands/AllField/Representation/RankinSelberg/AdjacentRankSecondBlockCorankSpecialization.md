# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockCorankSpecialization`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankSecondBlockCorankSpecialization` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockCorankSpecialization`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockCorankSpecialization` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Entire corank coefficients of the actual second-block family and their initial clearing.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankEntireCoefficientSpecialization`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.corankCoefficientSeries` (def): The actual bilateral coefficient series of one corank integral.
- `Langlands.AllField.RankinSelberg.Padic.SecondBlockCorankRealRayClearing` (def): Formal clearing on a real ray for every actual coefficient of the second
  deformed lower induction. This is an input, separate from integral analyticity.
- `Langlands.AllField.RankinSelberg.Padic.secondBlock_entireCorankFamily` (theorem): Every original coefficient extends to an actual second-block Whittaker
  family whose corank slices are integrable and entire for the supplied measure.
- `Langlands.AllField.RankinSelberg.Padic.secondBlock_corankClearing_at_zero` (theorem): Clearing every actual deformed coefficient above a real bound clears the
  specified original coefficient by the original product polynomial.
