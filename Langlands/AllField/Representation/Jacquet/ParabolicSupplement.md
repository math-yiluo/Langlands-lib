# All-field supplement to `Langlands.AllField.Representation.Jacquet.Parabolic`

`Langlands.AllField.Representation.Jacquet.ParabolicSupplement` supplements the Library module `Langlands.AllField.Representation.Jacquet.Parabolic`, the existing all-field port of `Langlands.Representation.Jacquet.Parabolic`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.Jacquet.Parabolic` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Jacquet.Parabolic` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized Jacquet modules for standard block parabolics**

The Jacquet module of a representation of `GL_n` along a standard block parabolic
is the actual coinvariant quotient of its restriction to the parabolic by the
unipotent radical. The Levi acts through its section into the parabolic,
normalized by the inverse square root of a supplied full positive modulus. For
p-adic fields that modulus is the explicit block modulus.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Representation.Jacquet.Parabolic`

## Declarations

- `Langlands.LocalFieldData.normalizedJacquetMap` (def): The Jacquet map of an actual intertwiner.

Declarations of the original re-declared by `Langlands.AllField.Representation.Jacquet.Parabolic` and therefore not here: `Langlands.PadicField.TopologicalData.normalizedJacquet`, `Langlands.PadicField.TopologicalData.normalizedJacquet_mk`, `Langlands.PadicField.TopologicalData.normalizedJacquet_mk_eq_inv_halfModulus`, `Langlands.PadicField.TopologicalData.isSmooth_normalizedJacquet`, `Langlands.PadicField.TopologicalData.normalizedJacquetFunctor`.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.JacquetModule`, `Langlands.GeneralLinear.BlockShape.jacquetMk`, `Langlands.GeneralLinear.BlockShape.jacquetMk_surjective`, `Langlands.GeneralLinear.BlockShape.top_le_normalizer_unipotentRadical`, `Langlands.GeneralLinear.BlockShape.leviToTop`, `Langlands.GeneralLinear.BlockShape.leviToTop_val`, `Langlands.GeneralLinear.BlockShape.topModulus`, `Langlands.GeneralLinear.BlockShape.topModulus_leviToTop`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetOf`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetOf_mk`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetOfMap`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetOfMap_mk`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetOfMap_id`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetOfMap_comp`, `Langlands.GeneralLinear.BlockShape.jacquetModuleEquiv`, `Langlands.GeneralLinear.BlockShape.jacquetModuleEquiv_mk`, `Langlands.GeneralLinear.BlockShape.isOpen_ker_topModulus`, `Langlands.GeneralLinear.BlockShape.continuous_leviToTop`, `Langlands.GeneralLinear.BlockShape.isSmooth_normalizedJacquetOf`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetObjectOf`, `Langlands.GeneralLinear.BlockShape.normalizedJacquetFunctorOf`, `Langlands.PadicField.canonicalNormalizedJacquet`, `Langlands.PadicField.canonicalNormalizedJacquetFunctor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
