# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankShellConvolution`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankShellConvolution` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankShellConvolution`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankShellConvolution` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The finite determinant-shell convolution in JPSS Section 6.3, (8)--(10).

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankQuotientShear`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.adjacentRankInnerMultiplier` (def): The actual continuous character and norm multiplier in the inner integral.
- `Langlands.AllField.RankinSelberg.Padic.continuous_adjacentRankInnerMultiplier` (theorem).
- `Langlands.AllField.RankinSelberg.Padic.hasCompactSupport_equalRankSlice` (theorem): The equal-rank integrand at zero has compact support on every quotient
  slice when its first member is an actual smooth coefficient-image vector.
- `Langlands.AllField.RankinSelberg.Padic.integrable_equalRankSlice` (theorem): In particular every such equal-rank slice is genuinely integrable against
  any Borel quotient measure finite on compact sets.
- `Langlands.AllField.RankinSelberg.Padic.integral_eq_sum_determinantSlices` (theorem): A finite support bound in determinant order gives an exact finite partition
  of the integral. The bound concerns actual pointwise support.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankJointShellKernel_mk_eq_innerSlice` (theorem): On a fixed quotient slice, the joint cutoff is precisely the complementary
  group slice. This is the pointwise identity underlying the convolution.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.Padic.adjacentRankShell_finiteConvolution`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
