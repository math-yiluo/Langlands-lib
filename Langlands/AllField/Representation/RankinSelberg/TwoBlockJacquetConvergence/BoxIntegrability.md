# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Integrability from geometric bounds on an exhaustion by boxes**

A measurable function `f` is integrable as soon as there are measurable sets `box e`
with `μ(box e) ≤ M Q^e` and, for every point `x`, some `e` with `x ∈ box e` and
`|f x| ≤ C s^e`, where `s Q < 1`: then `|f| ≤ ∑_e C s^e 1_(box e)`, whose integral
is a convergent geometric series. On a rectangular matrix space over a p-adic field the
boxes `{x : ϖ^e x_(ab) ∈ O}` have measure `(q^e μ(O))^(jl)` by the scalar Haar scaling.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.box` (def): The box `{x : ϖ^e x_(ab) ∈ O}` of a rectangular matrix space.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.box_eq_pi` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.measurableSet_box` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.measure_preimage_uniformizer_pow_mul` (theorem): The scalar lattice `ϖ^(-e) O` has measure `q^e μ(O)`.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.rectangularMeasure_box` (theorem): The measure of a box of a rectangular matrix space.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockConvergence.integrable_of_forall_exists_mem_box`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
