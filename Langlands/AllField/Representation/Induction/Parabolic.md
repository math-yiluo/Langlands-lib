# All-field port of `Langlands.Representation.Induction.Parabolic`

`Langlands.AllField.Representation.Induction.Parabolic` is the all-field port of the Library module `Langlands.Representation.Induction.Parabolic`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Induction.Parabolic` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized parabolic induction from standard block Levi subgroups**

A representation of the actual block Levi is inflated along the block projection
of the standard upper block parabolic, twisted by the inflated normalizing
character, and smoothly induced by right translation. For p-adic fields the
normalizing character is the positive square root of the explicit block modulus.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`

## Declarations

- `Langlands.LocalFieldData.leviHalfCharacter` (def): The positive half `δ_P^(1/2)` of the explicit block modulus, as a smooth Levi
  character for the selected realization.
- `Langlands.LocalFieldData.leviHalfCharacter_toMonoidHom` (theorem).
- `Langlands.LocalFieldData.normalizedParabolicInduced` (def): Normalized parabolic induction `i_P^G σ` for an actual p-adic field: smooth
  induction by right translation of `δ_P^(1/2) ⊗ σ`, inflated to the parabolic.
- `Langlands.LocalFieldData.normalizedParabolicInduced_covariant` (theorem): The covariance `f (p g) = δ_P(m)^(1/2) σ(m) f(g)` with `m` the Levi part of `p`.
- `Langlands.LocalFieldData.isSmooth_normalizedParabolicInduced` (theorem).
- `Langlands.LocalFieldData.normalizedParabolicInducedMap` (def): The induced map of an actual Levi intertwiner.
- `Langlands.LocalFieldData.normalizedParabolicInductionFunctor` (def): Normalized parabolic induction as a functor of canonical smooth categories.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.inflateCharacter`, `Langlands.GeneralLinear.BlockShape.inflateCharacter_apply`, `Langlands.GeneralLinear.BlockShape.inducingRepresentation`, `Langlands.GeneralLinear.BlockShape.normalizedInducedOf`, `Langlands.GeneralLinear.BlockShape.normalizedInducedOf_covariant`, `Langlands.GeneralLinear.BlockShape.normalizedInducedOf_apply`, `Langlands.GeneralLinear.BlockShape.isSmooth_normalizedInducedOf`, `Langlands.GeneralLinear.BlockShape.normalizedCompactInducedOf`, `Langlands.GeneralLinear.BlockShape.isSmooth_normalizedCompactInducedOf`, `Langlands.GeneralLinear.BlockShape.normalizedCompactInclusionOf`, `Langlands.GeneralLinear.BlockShape.inducingMap`, `Langlands.GeneralLinear.BlockShape.normalizedInducedOfMap`, `Langlands.GeneralLinear.BlockShape.normalizedInducedOfMap_apply`, `Langlands.GeneralLinear.BlockShape.normalizedInducedOfMap_id`, `Langlands.GeneralLinear.BlockShape.normalizedInducedOfMap_comp`, `Langlands.GeneralLinear.BlockShape.normalizedInductionFunctorOf`, `Langlands.PadicField.TopologicalData.normalizedParabolicCompactInduced`, `Langlands.PadicField.TopologicalData.normalizedParabolicCompactInclusion`, `Langlands.PadicField.canonicalNormalizedParabolicInduced`, `Langlands.PadicField.canonicalNormalizedParabolicInductionFunctor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
