# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankJacquetCovariance`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetCovariance` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetCovariance`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetCovariance` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Standard Whittaker covariance for the actual adjacent lower Jacquet integral.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetLinear`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentJacquet.measurePreserving_unipotentShift` (theorem): The affine unipotent substitution preserves the supplied additive row Haar.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.measurableEmbedding_unipotentShift` (theorem): The same literal substitution is a measurable embedding.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.tensorCoordinates_lowerBlock_action` (theorem): The lower normalized inducing action is exactly σ(a) on a unipotent
  head block: both determinant weights are one.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.sectionCoefficient_lowerBlock` (theorem): Left multiplication by a unipotent lower diagonal block acts through the
  specified original-carrier Whittaker functional.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrand_unipotent_mul` (theorem): The literal kernel transforms by the standard ambient character and the
  measure-preserving affine column substitution.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integral_unipotent_mul` (theorem): Integration of the exact substitution gives standard Whittaker covariance.
  This equality of totalized integrals needs no added convergence premise.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.functional` (def): Under actual all-section integrability, the scalar Jacquet integral at the
  identity is a standard Whittaker functional on the exact host induction.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.functional_coefficient` (theorem): Every coefficient of this single original-carrier functional is the literal
  Jacquet integral at that ambient group element.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.AdjacentJacquet.unipotentHead`, `Langlands.RankinSelberg.AdjacentJacquet.unipotentHead_apply`, `Langlands.RankinSelberg.AdjacentJacquet.unipotentHead_mem`, `Langlands.RankinSelberg.AdjacentJacquet.unipotentColumn`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlock`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlock_castSucc_castSucc`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlock_castSucc_last`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlock_last_castSucc`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlock_last_last`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlockParabolic`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlockParabolic_largeProjection`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlock_mem`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_mul`, `Langlands.RankinSelberg.AdjacentJacquet.lowerBlock_mul_upperColumn`, `Langlands.RankinSelberg.AdjacentJacquet.unipotent_decomposition`, `Langlands.RankinSelberg.AdjacentJacquet.unipotentShift`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_mul_unipotent`, `Langlands.RankinSelberg.AdjacentJacquet.unipotent_mulVec_last`, `Langlands.RankinSelberg.AdjacentJacquet.unipotentShift_last`, `Langlands.RankinSelberg.AdjacentJacquet.unipotent_superdiagonal_sum`, `Langlands.RankinSelberg.AdjacentJacquet.standardCharacter_split`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
