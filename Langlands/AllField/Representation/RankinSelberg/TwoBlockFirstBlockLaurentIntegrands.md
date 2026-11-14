# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The two large integrands on the first-block fibers**

On the fiber `[diag(v, 1) R(y; x) g]` the upper integrand is the actual unequal-rank
integrand at `s = 0` of the right translate of the test function by `R(0; x) g` and the
first-block coefficient function of `f(g)`, times `Φ((x, η) g)`. On the fiber
`[diag(v, 1) g]` the lower integrand is the corresponding inverse half modulus times the
partial Fourier value. At the reflected point `[w v^ι]`, the transformed small integrand
of the translate by `R(0; x) g` is `ψ((x v⁻¹)_0)` times the block-rotated test value.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentFourier`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.whittaker_blockRotation_firstBlockEmbedding_lowerRadical` (theorem): `W(C diag(v, 1) R(0; x) g) = ψ((x v⁻¹)_0) W(C diag(v, 1) g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.upperIntegrand_fiberPoint_rowSnoc` (theorem): On the fiber `[diag(v, 1) R(y; x) g]`, the upper integrand is the actual unequal-rank
  integrand at `s = 0` of the translate of the test function by `R(0; x) g` and the
  first-block coefficient function of `f(g)`, times `Φ((x, η) g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.lowerIntegrand_firstBlockFiberPoint` (theorem): On the fiber `[diag(v, 1) g]`, the lower integrand is the block-rotated test value, the
  inverse half modulus times the first-block coefficient, and the partial Fourier value.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.dualIntegrand_reflectionQuotient` (theorem): At the reflected point `[w v^ι]`, the transformed small integrand is the
  block-rotated value `W(C diag(v, 1))` times `W'(v)` and the reflected determinant weight.
