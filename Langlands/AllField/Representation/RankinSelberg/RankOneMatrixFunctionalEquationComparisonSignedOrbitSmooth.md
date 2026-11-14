# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Smooth standard-character functions from the actual signed matrix orbit.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticBridge`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof`
- `Langlands.AllField.Representation.Shahidi.Induction`

## Declarations

- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.signedMatrixOrbit` (def): The actual signed inverse-transpose orbit of one ambient matrix test.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.signedMatrixOrbit_left` (theorem): Signed reflection and right Haar substitution give the same standard
  character, rather than its inverse.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.exists_signedMatrixOrbit_congruence` (theorem): A single principal congruence subgroup fixes the entire orbit function.
  No regularity of a parameter-dependent integral is assumed.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedSignedMatrixOrbit` (def): The determinant-weighted signed orbit function for any complex exponent.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedSignedMatrixOrbit_left` (theorem): The determinant twist is trivial on upper unipotents, so it retains
  the same standard-character covariance.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.exists_weightedSignedMatrixOrbit_stabilizer` (theorem): Intersecting a congruence subgroup with the open determinant-character
  kernel supplies a uniform open stabilizer of the weighted orbit.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedSignedMatrixOrbitSmooth` (def): The actual weighted orbit as a smooth induced standard-character function.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedSignedMatrixOrbitSmooth_eval` (theorem).
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedSignedMatrixOrbit_locallyConstant` (theorem): In particular the entire weighted orbit is locally constant.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.CompactWhittakerSynthesis.continuous_weightedSignedMatrixOrbit`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
