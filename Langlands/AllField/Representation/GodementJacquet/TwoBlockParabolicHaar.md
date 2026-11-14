# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockParabolicHaar` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Haar measure of `GL_(t+1)` in two-block parabolic coordinates**

For the upper parabolic `P` of the block shape `(m 0 + 1, m 1 + 1)`, every element
of `P` is `parabolicPoint (L, x) = leviEmbedding L * upperRadical x`, whose matrix is
`[[a, a x], [0, d]]` for `L = (a, d)`. With the parameter measure
`parabolicMeasure = (∏ normalized block Haar measures) × dx` (no density), left
translation in `P` is measure preserving, and for every compact open `K` with
`GL_(t+1) = P K` the Haar measure of `GL_(t+1)` factors through `K × P`
(Godement–Jacquet 1972, printed page 38, in its two-block form).

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell`

## Declarations

- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicMeasure` (def): The parameter measure `dL × dx` on `Levi × Mat_{(m 0 + 1) × (m 1 + 1)}`, with the
  normalized Haar measures of the blocks and a supplied measure `dx` on the radical.
- `Langlands.AllField.GodementJacquet.TwoBlock.measurable_parabolicPoint` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicMeasure_sigmaFinite` (instance).
- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicMeasure_isOpenPosMeasure` (instance).
- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicMeasure_isFiniteMeasureOnCompacts` (instance).
- `Langlands.AllField.GodementJacquet.TwoBlock.measurePreserving_parabolicShift` (theorem): Left translations of the parabolic are measure-preserving in parabolic coordinates.
- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicPoint_translation` (theorem): The parameter-space form of left translation required by the factorization integral.
- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicMeasure_preimage_ne_zero` (theorem): The parameters of an open subgroup have positive measure.
- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicMeasure_preimage_ne_top` (theorem): The parameters of a compact subgroup have finite measure.
- `Langlands.AllField.GodementJacquet.TwoBlock.map_mul_left_radical` (theorem): Left multiplication by `a ∈ GL_(m 0 + 1)` scales the radical measure by `|det a|^(-(m 1 + 1))`.
- `Langlands.AllField.GodementJacquet.TwoBlock.measurableEmbedding_mul_left_radical` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.integral_mul_left_radical` (theorem): **Radical scaling.** `∫ Ψ (a x) dx = |det a|^(-(m 1 + 1)) ∫ Ψ dx`.
- `Langlands.AllField.GodementJacquet.TwoBlock.integrable_mul_left_radical_iff` (theorem): Integrability is unchanged by the radical scaling.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.TwoBlock.blockEquiv`, `Langlands.GodementJacquet.TwoBlock.blockEquiv_inl`, `Langlands.GodementJacquet.TwoBlock.blockEquiv_inr`, `Langlands.GodementJacquet.TwoBlock.val_eq_reindex_fromBlocks`, `Langlands.GodementJacquet.TwoBlock.leviEmbedding_val`, `Langlands.GodementJacquet.TwoBlock.upperRadical_val`, `Langlands.GodementJacquet.TwoBlock.reindex_mul_reindex`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint_val`, `Langlands.GodementJacquet.TwoBlock.upperRadical_mul_leviEmbedding`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint_inv_mul`, `Langlands.GodementJacquet.TwoBlock.corner`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint_mem`, `Langlands.GodementJacquet.TwoBlock.parabolicCoord`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint_parabolicCoord`, `Langlands.GodementJacquet.TwoBlock.parabolicCoord_parabolicPoint`, `Langlands.GodementJacquet.TwoBlock.exists_parabolicPoint_eq`, `Langlands.GodementJacquet.TwoBlock.det_parabolicPoint`, `Langlands.GodementJacquet.TwoBlock.exists_parabolicPoint_mul`, `Langlands.GodementJacquet.TwoBlock.parabolicShift`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint_parabolicShift`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint_one_zero`, `Langlands.GodementJacquet.TwoBlock.continuous_parabolicPoint`, `Langlands.GodementJacquet.TwoBlock.continuous_corner`, `Langlands.GodementJacquet.TwoBlock.continuous_parabolicCoord`, `Langlands.GodementJacquet.TwoBlock.integrable_parabolic_iff`, `Langlands.GodementJacquet.TwoBlock.integral_parabolic`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
