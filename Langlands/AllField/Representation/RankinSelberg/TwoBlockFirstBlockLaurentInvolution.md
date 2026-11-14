# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The reflection `[v] ↦ [w v^ι]` of the small quotient**

On `N \ GL_(n+1)` the map `[v] ↦ [w v^ι]`, with `w` the long Weyl element and `ι` the
inverse transpose, is a well-defined involutive homeomorphism. It preserves every
compatible quotient measure and exchanges the determinant slices `k` and `-k`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionQuotient_mem_determinantSlice` (theorem): The reflection exchanges the determinant slices `k` and `-k`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.measurePreserving_reflectionQuotient` (theorem): The reflection preserves every compatible quotient measure on the small quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.setIntegral_determinantSlice_reflectionQuotient` (theorem): Change of variables by the reflection on determinant slices.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.mulEquivHaarChar_eq_one_of_involutive`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionAut`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionAut_apply`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionAut_involutive`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionAut_mem_iff`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionQuotient`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionQuotient_mk`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.reflectionQuotient_involutive`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.abv_det_weylLong`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.abv_det_weylLong_mul_inverseTranspose`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
