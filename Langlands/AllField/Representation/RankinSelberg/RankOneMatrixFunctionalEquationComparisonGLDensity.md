# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The determinant density relating matrix additive Haar and actual GL Haar.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof`

## Declarations

- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.padic_weightedRestriction_isHaar` (theorem): The genuine residue-normalized determinant density gives Haar measure for
  every supplied p-adic realization and every additive matrix Haar measure.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.padic_exists_weightedRestriction_eq_generalLinearHaar` (theorem): Comparison with the canonical actual GL Haar measure, normalized on integral
  matrices. The scalar is positive and depends on the supplied additive measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_comp`, `Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv`, `Langlands.RankinSelberg.GLDeterminantDensity.matrixWeight`, `Langlands.RankinSelberg.GLDeterminantDensity.weight`, `Langlands.RankinSelberg.GLDeterminantDensity.weight_eq`, `Langlands.RankinSelberg.GLDeterminantDensity.weight_ne_zero`, `Langlands.RankinSelberg.GLDeterminantDensity.weight_mul`, `Langlands.RankinSelberg.GLDeterminantDensity.weight_inv`, `Langlands.RankinSelberg.GLDeterminantDensity.continuous_weight`, `Langlands.RankinSelberg.GLDeterminantDensity.measurable_matrixWeight`, `Langlands.RankinSelberg.GLDeterminantDensity.additiveRestriction`, `Langlands.RankinSelberg.GLDeterminantDensity.additiveRestriction_map_left`, `Langlands.RankinSelberg.GLDeterminantDensity.weightedRestriction`, `Langlands.RankinSelberg.GLDeterminantDensity.weightedRestriction_leftInvariant`, `Langlands.RankinSelberg.GLDeterminantDensity.weightedRestriction_isHaar`, `Langlands.RankinSelberg.GLDeterminantDensity.weightedRestriction_map`, `Langlands.RankinSelberg.GLDeterminantDensity.weightedRestriction_map_ambient`, `Langlands.RankinSelberg.GLDeterminantDensity.exists_weightedRestriction_eq_smul`, `Langlands.RankinSelberg.GLDeterminantDensity.integrable_weightedRestriction_iff`, `Langlands.RankinSelberg.GLDeterminantDensity.integral_weightedRestriction`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
