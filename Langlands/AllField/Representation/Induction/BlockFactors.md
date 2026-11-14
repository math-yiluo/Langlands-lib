# All-field port of `Langlands.Representation.Induction.BlockFactors`

`Langlands.AllField.Representation.Induction.BlockFactors` is the all-field port of the Library module `Langlands.Representation.Induction.BlockFactors`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Induction.BlockFactors` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized induction of block factors**

For representations `σ_1, …, σ_r` of the diagonal blocks `GL_{n_i}`, the actual
block Levi acts on their external tensor product, and normalized parabolic
induction from the standard upper block parabolic gives the representation
`i(σ_1, …, σ_r)` of `GL_n`.

## Imports from the port

- `Langlands.AllField.Representation.Induction.Parabolic`

## Declarations

- `Langlands.LocalFieldData.normalizedProductInduced` (def): Henniart's `i(σ_1, …, σ_r)` for an actual p-adic field: normalized parabolic
  induction, from the standard upper block parabolic with the successive block
  sizes, of the tensor product of the block representations.
- `Langlands.LocalFieldData.normalizedProductInduced_covariant` (theorem): The covariance `f (p g) = δ_P(m)^(1/2) (σ_1(m_1) ⊗ ⋯ ⊗ σ_r(m_r)) (f g)`,
  with `m = (m_1, …, m_r)` the Levi part of `p`.
- `Langlands.LocalFieldData.isSmooth_normalizedProductInduced` (theorem).
- `Langlands.LocalFieldData.normalizedProductInducedMap` (def): The induced map of a family of actual block intertwiners.
- `Langlands.LocalFieldData.normalizedProductInductionFunctor` (def): `i(σ_1, …, σ_r)` as a functor from families of smooth block representations
  to smooth representations of `GL_n(F)`.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.blockTensor`, `Langlands.GeneralLinear.BlockShape.blockTensor_tprod`, `Langlands.GeneralLinear.BlockShape.productInducedOf`, `Langlands.GeneralLinear.BlockShape.productInducedOf_eq`, `Langlands.GeneralLinear.BlockShape.productInducedOf_covariant`, `Langlands.GeneralLinear.BlockShape.productInducedOf_apply`, `Langlands.GeneralLinear.BlockShape.isSmooth_productInducedOf`, `Langlands.GeneralLinear.BlockShape.productInducedOfMap`, `Langlands.GeneralLinear.BlockShape.productInducedOfMap_apply`, `Langlands.GeneralLinear.BlockShape.productInducedOfMap_id`, `Langlands.GeneralLinear.BlockShape.productInducedOfMap_comp`, `Langlands.GeneralLinear.BlockShape.productInductionFunctorOf`, `Langlands.GeneralLinear.BlockShape.productInductionFunctorOf_obj`, `Langlands.PadicField.TopologicalData.normalizedProductInduced_eq`, `Langlands.PadicField.TopologicalData.normalizedProductCompactInduced`, `Langlands.PadicField.TopologicalData.normalizedProductCompactInclusion`, `Langlands.PadicField.TopologicalData.normalizedProductInducedMap_id`, `Langlands.PadicField.TopologicalData.normalizedProductInducedMap_comp`, `Langlands.PadicField.TopologicalData.normalizedProductInductionFunctor_obj`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

Not ported on purpose: `Langlands.PadicField.canonicalNormalizedProductInduced`, `Langlands.PadicField.canonicalNormalizedProductInductionFunctor`. These are canonical-data wrappers, lemmas comparing two realizations of the same p-adic field, or facts that `Langlands.AllField.LocalField.Foundation` and `Langlands.LocalFactor.LocalAbelian` already provide for every local field; the port works with one supplied realization throughout.
