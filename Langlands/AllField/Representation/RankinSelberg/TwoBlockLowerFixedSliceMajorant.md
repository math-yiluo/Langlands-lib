# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**A concrete cone majorant for the Section 4.7 lower integrand**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerCompactFourier`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerIntegralRotation`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.blockRotation_inv_mul_torus` (theorem): Moving the inverse block rotation through the canonical torus permutes its
  integer exponents.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_rotated_section_growth` (theorem): Section growth in the rotated coordinates, with the exact opposing twist
  and all remaining diagonal growth absorbed into a single fixed base.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.integrand_standard_mk` (theorem): Exact representative formula for the integrand transported to the standard
  quotient. The test coefficient is evaluated without a left rotation.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_integrand_torus_majorant` (theorem): One fixed growth base works for every later section, coefficient and row
  Schwartz function. Nonzero values are confined to an opposing cone.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.diagonalDensity_nonneg` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_summable_integrand_majorant` (theorem): A single real threshold, before all later analytic inputs, yields a uniform
  compact bound whose product with the exact Iwasawa density is summable.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFixedSlice.coneMajorant`, `Langlands.RankinSelberg.TwoBlockLowerFixedSlice.coneMajorant_nonneg`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
