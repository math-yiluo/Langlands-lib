# All-field port of `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`

`Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof` is the all-field port of the Library module `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.Unramified.SphericalConstituentExistenceProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Existence of spherical constituents of unramified principal series**

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Group.GL.UnramifiedCharacterSupplement`
- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`
- `Langlands.AllField.Representation.Induction.BlockFactors`
- `Langlands.AllField.Representation.Jacquet.ParabolicSupplement`
- `Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof`
- `Langlands.AllField.Representation.Parabolic.NormalizedInductionStatementSupplement`
- `Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement`

## Declarations

- `Langlands.AllField.Unramified.SphericalExistence.exists_compactOpenSubgroup_le` (theorem): Every open subgroup of `GL_(r+1)(F)` contains a compact open subgroup.

Public declarations of the original that are not re-declared here: `Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective`, `Langlands.Unramified.SphericalExistence.exists_fixed_smoothFunction`, `Langlands.Unramified.SphericalExistence.determinantNorm_eq_one_of_integral`, `Langlands.Unramified.SphericalExistence.leviProjection_mem_normOneLevi`, `Langlands.Unramified.SphericalExistence.blockCharacters`, `Langlands.Unramified.SphericalExistence.borelInducing`, `Langlands.Unramified.SphericalExistence.sphericalTensor`, `Langlands.Unramified.SphericalExistence.sphericalTensor_ne_zero`, `Langlands.Unramified.SphericalExistence.borelInducing_sphericalTensor`, `Langlands.Unramified.SphericalExistence.exists_borel_mul_spherical`, `Langlands.Unramified.SphericalExistence.blockCharacters_isAdmissible`, `Langlands.Unramified.SphericalExistence.principalSeriesOfTuple_isAdmissible`, `Langlands.Unramified.SphericalExistence.sphericalConstituentExistence`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
