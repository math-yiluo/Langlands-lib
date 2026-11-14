# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Integral normalization of the lower mixed Haar**

The actual lower mixed integral subgroup has normalized mass one. The product
formed from any supplied rectangular Haar has mass equal to its integral cube.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasures`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedIntegralOpen` (def): Actual integral points in the lower mixed subgroup, as a compact open subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedIntegralOpen_isCompact` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedHaar` (def): Haar measure chosen before any rectangular measure and normalized on the
  actual integral points.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedHaar_isHaar` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedHaar_regular` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedHaar_integral` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.normOneHaar_integral` (theorem): The restriction-normalized norm-one Haar gives its integral subgroup mass one.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixed_preimage_integral` (theorem): Integral points in the actual coordinates form the three expected integral sets.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedProductMeasure_eq_smul` (theorem): The coefficient of the coordinate product is the supplied integral-cube mass.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedHaar_isMulRightInvariant` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixed_compatibleMeasureExists` (theorem): Compatible quotient existence for the one normalized lower mixed Haar.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct_mem_integralSubgroup_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
