# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankDualEntireCoefficientFamily`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankDualEntireCoefficientFamily` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankDualEntireCoefficientFamily`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankDualEntireCoefficientFamily` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Entire determinant-slice coefficients for the actual Weyl-translated dual family.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankEntireCoefficientSpecialization`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.HasCommonCompactOpenRightLevel.translate` (theorem): A fixed right translation conjugates one common compact open level.
- `Langlands.AllField.RankinSelberg.Padic.HasCommonCompactOpenRightLevel.firstDual` (theorem): Inverse transpose pulls one common compact open level back to a common
  compact open level for the actual first dual functions.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankDualWhittakerFamily` (def): The actual first dual transform, followed by the block Weyl translation
  in the adjacent functional equation.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankDualWhittakerFamily_level_entire` (theorem): The actual translated dual family retains a common compact open right
  level and pointwise entire parameter dependence.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankDualCoefficientFamily` (def): The literal coefficients of the actual adjacent dual integral at spectral
  parameter zero, for the same original test model vector.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankDualCoefficientFamily_integrable_entire` (theorem): The published corank slice theorem applies to the actual dual test model
  and actual translated dual family, giving both integrability and entire
  dependence of every literal dual determinant-slice coefficient.
