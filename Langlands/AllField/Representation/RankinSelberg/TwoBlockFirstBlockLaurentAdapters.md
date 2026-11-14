# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentAdapters`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentAdapters` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentAdapters`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentAdapters` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Adapters for the first-block Laurent assembly**

The descended row character `[v] ↦ ψ((x v⁻¹)_0)` on the small quotient, joint
measurability of the fiber maps, and the vanishing of the two large integrands when
the test functional or the first block functional is zero.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.firstRowCharacter` (def): The row character `[v] ↦ ψ((x v⁻¹)_0)` on `N \ GL_(n+1)`, by actual descent: right
  multiplication of a row by an upper unipotent matrix does not change its first entry.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.firstRowCharacter_mk` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.norm_firstRowCharacter` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.continuous_firstRowCharacter` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.aestronglyMeasurable_firstRowCharacter` (theorem): Joint almost-everywhere strong measurability of the row character for every measure
  on the product of rows and the Borel small quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.aestronglyMeasurable_comp_fiberPoint_lowerRadical` (theorem): Joint almost-everywhere strong measurability of `(Z, q) ↦ E([diag(v_q, 1) R(Z) g])`
  for continuous `E`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.scalarSection_eq_zero_of_first` (theorem): A zero first functional makes every scalar section vanish.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.upperIntegrand_eq_zero_of_first` (theorem): The upper integrand vanishes for a zero first functional.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.upperIntegrand_eq_zero_of_test` (theorem): The upper integrand vanishes for a zero test function.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.lowerIntegrand_eq_zero_of_first` (theorem): The lower integrand vanishes for a zero first functional.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.lowerIntegrand_eq_zero_of_test` (theorem): The lower integrand vanishes for a zero test function.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.coefficientModel_val_eq_zero` (theorem): Every vector of the coefficient image of a zero functional is the zero function.
