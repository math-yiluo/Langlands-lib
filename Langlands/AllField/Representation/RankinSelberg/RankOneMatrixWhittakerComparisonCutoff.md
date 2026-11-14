# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Fourier cutoff along the rank-one embedding**

For `σ` smooth on `GL_(m+2)`, a standard functional `ℓ`, a model function `W` of `ℓ`
and a Schwartz–Bruhat function `φ` on `F`, there is a model function `W'` of the
same `ℓ` with `W'(diag(det g, 1, …, 1)) = φ(det g) W(diag(det g, 1, …, 1))` for every
`g ∈ GL₁`. The function `W'` is the right smearing of `W` along `x ↦ 1 + x E₀₁`
against a Fourier preimage of `φ`.

## Imports from the port

- `Langlands.AllField.Group.GL.MirabolicTailConullProof`
- `Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsProof`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.exists_rankOneCutoff` (theorem): The Fourier cutoff along `rankOneEmbedding m` for the canonical topology of a
  p-adic field: every `φ(det g)` multiple of a model function on the embedded `GL₁` is
  the restriction of a model function of the same functional.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rankOneCutoff_index_ne`, `Langlands.RankinSelberg.rankOneCutoffUnipotent`, `Langlands.RankinSelberg.rankOneCutoffUnipotent_apply`, `Langlands.RankinSelberg.rankOneCutoffUnipotent_mem`, `Langlands.RankinSelberg.rankOneEmbedding_mul_cutoffUnipotent`, `Langlands.RankinSelberg.standardCharacter_rankOneCutoffUnipotent`, `Langlands.RankinSelberg.exists_rankOneCutoff_of_isSelfDual`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
