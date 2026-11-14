# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankJacquetLinear`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetLinear` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetLinear`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetLinear` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetEvaluation`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentJacquet.inducedRepresentation` (abbrev): The exact normalized opposite-parabolic representation in the host statement.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.sectionCoefficientLinear` (def): The original-carrier scalar evaluation is linear in the actual induced section.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.sectionCoefficientLinear_apply` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.sectionCoefficient_right` (theorem): Right translation of an actual induced section evaluates by right multiplication.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrandLinear` (def): The literal Jacquet kernel is linear in the original induced section.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrandLinear_apply` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrand_right` (theorem): The Jacquet kernel commutes with the exact right action on the host induction.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integral` (def): The actual scalar Jacquet integral, before imposing its convergence hypothesis.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integral_right` (theorem): Integrating the exact right-translation identity gives coefficient evaluation.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integralLinear` (def): On any family of actual sections with absolute convergence, scalar integration
  is a linear map. The hypothesis is discharged by section spanning in the image proof.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integralLinear_apply` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integralLinear_coefficient` (theorem): The integral at the identity has exactly the scalar Jacquet coefficients at every g.
