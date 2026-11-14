# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDeformationCell`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDeformationCell`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDeformationCell` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The upper radical of the lower two-block induction**

For the lower two-block induction `I(σ_1 ⊗ σ_2)` of `GL_(t+1)` with blocks of sizes
`m 0 + 1` and `m 1 + 1`, and the complementary upper radical `u(x) = [[1, x], [0, 1]]`,
this module proves the block factorization `u(x) n = diag(n_0, n_1) u(n_0⁻¹ (β + x n_1))`
of an upper unipotent matrix `n` with diagonal blocks `n_0, n_1` and upper-right block
`β`, the corresponding decomposition of the first-superdiagonal sum, and the
consequences for sections: the subspace of sections whose restriction to the upper
radical has compact support is stable under the upper unipotent group, and the
scalar integral `f ↦ ∫ ⟨f(u(x)), ⊗ λ_i⟩ ψ(x_(m 0, 0)) dx` is `ψ⁻¹`-equivariant for
block functionals `λ_i` equivariant for the inverse standard characters.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData`
- `Langlands.AllField.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.determinantNorm_eq_one_of_mem_upperUnipotent` (theorem): An upper unipotent matrix has determinant norm one.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.leviModulus_eq_one` (theorem): The block modulus is trivial on Levi elements whose blocks have determinant norm one.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.sectionEval_leviEmbedding_mul` (theorem): Left translation by a Levi element with determinant-norm-one blocks acts on values by
  the block tensor representation.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.radicalRestriction` (def): The restriction `x ↦ f(u(x))` of a section to the upper radical.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.radicalRestriction_inducedRep` (theorem): An upper unipotent translate restricts through the block factorization.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.compactRadicalSubmodule` (def): The sections whose restriction to the upper radical has compact support.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.mem_compactRadicalSubmodule` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.inducedRep_mem_compactRadicalSubmodule` (theorem): The compact-radical sections are stable under the upper unipotent group.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.tensorContraction_blockTensor` (theorem): Block functionals equivariant for the inverse standard characters scale the
  contraction of a unipotent block translate by the product of the block characters.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.inverseStandardCharacter_eq_prod` (theorem): The inverse standard character of `n` is the product of the block characters of its
  diagonal blocks and the inverse character of its corner entry `β_(m 0, 0)`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.integral_comp_unipotentShift` (theorem): The coordinate change `x ↦ n_0⁻¹ (β + x n_1)` preserves every Borel additive Haar
  measure on the upper radical.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.jacquetFunction_inducedRep_upperUnipotent` (theorem): JPSS (4.6.2) at the identity is `ψ⁻¹`-equivariant under upper unipotent translation,
  for every section: `J(ρ(n) f)(1) = ψ⁻¹(n) J(f)(1)`. This is a change of variables and
  needs no integrability.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule` (theorem): Sections with compact radical restriction have absolutely integrable JPSS integrand at
  the identity, for every locally finite measure.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.compactRadicalJacquet` (def): JPSS (4.6.2) at the identity, as a linear functional on the compact-radical
  sections, given integrability there.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.compactRadicalJacquet_inducedRep` (theorem): The compact-radical functional is `ψ⁻¹`-equivariant under the upper unipotent group.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDeformation.val_index_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.val_index_one`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_index`, `Langlands.RankinSelberg.TwoBlockDeformation.mul_apply_index`, `Langlands.RankinSelberg.TwoBlockDeformation.ext_index`, `Langlands.RankinSelberg.TwoBlockDeformation.leviEmbedding_index_zero_one`, `Langlands.RankinSelberg.TwoBlockDeformation.leviEmbedding_index_one_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.upperUnipotent_index_one_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_radical_zero_zero_mul`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_mul_radical_zero_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_radical_one_one_mul`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_mul_radical_one_one`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_radical_zero_one_mul`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_mul_radical_zero_one`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_radical_one_zero_mul`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_mul_radical_one_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_levi_zero_one_mul`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_levi_one_zero_mul`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_mul_unipotent_one_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.unipotentLevi`, `Langlands.RankinSelberg.TwoBlockDeformation.unipotentLevi_apply`, `Langlands.RankinSelberg.TwoBlockDeformation.unipotentLevi_mem`, `Langlands.RankinSelberg.TwoBlockDeformation.unipotentCorner`, `Langlands.RankinSelberg.TwoBlockDeformation.unipotentShift`, `Langlands.RankinSelberg.TwoBlockDeformation.upperRadical_mul_upperUnipotent`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_superdiagonal_index`, `Langlands.RankinSelberg.TwoBlockDeformation.upperUnipotent_mul_apply_last`, `Langlands.RankinSelberg.TwoBlockDeformation.mul_upperUnipotent_apply_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.unipotentShift_last_zero`, `Langlands.RankinSelberg.TwoBlockDeformation.compactRadicalJacquet_apply`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
