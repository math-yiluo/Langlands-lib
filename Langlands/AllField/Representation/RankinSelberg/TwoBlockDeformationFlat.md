# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationFlat` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Flat sections of the two-block deformation**

For the lower block parabolic `Q̄` of `GL_(t+1)(F)` with blocks of sizes
`m 0 + 1` and `m 1 + 1`, and `K₀ = GL_(t+1)(O_F)`, every `g` factors as
`g = q k` with `q ∈ Q̄` and `k ∈ K₀`. The positive number
`κ(g) = |det q_0|`, the normalized absolute value of the determinant of the
first diagonal block of `q`, does not depend on the factorization. Multiplying
a section `f` of `ρ_0` by `κ(g)^u` gives a section `f_u` of `ρ_u`, and one
compact open subgroup fixes `f_u` for every complex `u`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.integralOpen` (def): The hyperspecial subgroup `K₀ = GL_(n+1)(O_F)` of the canonical realization,
  as an open subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.mem_integralOpen` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isCompact_integralOpen` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.inverseTranspose_mem_integralOpen` (theorem): The inverse transpose of an integral matrix is integral.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.mem_oppositeParabolic_of_lower` (theorem): An invertible matrix with zero entries above the diagonal lies in every lower block
  parabolic.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_oppositeParabolic_mul` (theorem): The lower Iwasawa decomposition `GL_(n+1)(F) = Q̄ K₀` for every block shape.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.determinantNorm_oppositeLeviProjection_of_mem` (theorem): The diagonal blocks of an element of `Q̄ ∩ K₀` have determinant of absolute value one.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.oppositeBlockNorm` (def): The norm `|det q_i|` of the `i`th diagonal block of the lower parabolic factor `q`
  of `g = q k`, `k ∈ K₀`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.oppositeBlockNorm_eq` (theorem): The block norm can be computed from any lower Iwasawa factorization.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.oppositeBlockNorm_pos` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.oppositeBlockNorm_mul_integral` (theorem): Right invariance under `K₀`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.oppositeBlockNorm_oppositeParabolic_mul` (theorem): Left covariance under the lower parabolic.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isLocallyConstant_oppositeBlockNorm` (theorem): The block norm is locally constant, being right invariant under the open subgroup `K₀`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.blockZeroNorm` (def): `κ(qk) = |det q_0|`: the first-block norm of the lower Iwasawa factor.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.blockZeroNorm_pos` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.blockZeroNorm_mul_integral` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.blockZeroNorm_oppositeParabolic_mul` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isLocallyConstant_blockZeroNorm` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.blockTensor_twoBlockDeformedBlocks` (theorem): The block tensor of the deformed blocks differs from the undeformed one by
  `|det a_0|^u`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatFunction` (def): The underlying function `g ↦ κ(g)^u f(g)` of a flat section.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatFunction_covariant` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatStabilizer` (def): The uniform stabilizer of the flat family through `f`: a chosen open stabilizer of `f`,
  intersected with `K₀`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatStabilizer_le_integralOpen` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.sectionEval_mul_flatStabilizer` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatFunction_mul_flatStabilizer` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatSection` (def): The flat section `f_u(g) = κ(g)^u f(g)` of `ρ_u` through a section `f` of `ρ_0`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatSection_zero` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_uniform_stabilizer` (theorem): One compact open subgroup fixes every member of the flat family through `f`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDeformation.oppositeBlockNorm_oppositeParabolic`, `Langlands.RankinSelberg.TwoBlockDeformation.oppositeBlockNorm_one`, `Langlands.RankinSelberg.TwoBlockDeformation.blockZeroNorm_oppositeParabolic`, `Langlands.RankinSelberg.TwoBlockDeformation.blockZeroNorm_one`, `Langlands.RankinSelberg.TwoBlockDeformation.sectionEval_flatSection`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
