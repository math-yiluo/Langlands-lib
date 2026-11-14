# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankMatrixReflection`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatrixReflection` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankMatrixReflection`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankMatrixReflection` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The actual reflected square-test scalar in the dual adjacent-rank formula.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankDualModelZetaCoefficient`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.adjacentRankDualMatrixReflectionScalar` (def): The scalar from reflecting the dual square test for the inverse
  determinant twist of an actual model coefficient.
- `Langlands.AllField.RankinSelberg.Padic.biSmoothModelCoefficient_minusOne` (theorem): Scalar action on the actual coefficient image gives the same scalar
  on every actual bi-smooth coefficient of its right-translation action.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankDualMatrixCoefficient_minusOne` (theorem): The actual inverse-transpose coefficient and inverse determinant
  character have the indicated central reflection scalar.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankMatrix_reflection` (theorem): Reflection preserves genuine matrix convergence, and the literal
  matrix integral changes by exactly the supplied central scalar.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankMatrix_reflectedRationalValue` (theorem): The actual shifted rational value of the reflected square test is the
  constant scalar multiple of the original shifted rational value.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankModelStar_reflectionScalar_cancel` (theorem): The model-star scalar and the square-test reflection leave precisely
  the actual second model's minus-one scalar.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankModelStar_reflectedProduct_cancel` (theorem): The same cancellation holds for the actual rational finite sum, so the
  reflection scalar changes the equal-rank sign by exactly one power.
