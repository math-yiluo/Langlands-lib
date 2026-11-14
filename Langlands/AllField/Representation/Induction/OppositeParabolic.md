# All-field port of `Langlands.Representation.Induction.OppositeParabolic`

`Langlands.AllField.Representation.Induction.OppositeParabolic` is the all-field port of the Library module `Langlands.Representation.Induction.OppositeParabolic`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Induction.OppositeParabolic` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized induction from opposite block parabolics**

A representation of the actual block Levi is inflated along the block projection
of the standard lower block parabolic, twisted by the inflated normalizing
character, and smoothly induced by right translation. For p-adic fields the
normalizing character is the inverse positive square root of the upper block modulus.

## Imports from the port

- `Langlands.AllField.Group.GL.PadicOppositeBlocks`
- `Langlands.AllField.Representation.Induction.Parabolic`

## Declarations

- `Langlands.LocalFieldData.oppositeLeviHalfCharacter` (def): The opposite induction half `δ_P^(-1/2)` of the upper block modulus.
- `Langlands.LocalFieldData.oppositeLeviHalfCharacter_toMonoidHom` (theorem).
- `Langlands.LocalFieldData.oppositeParabolicHalfModulus` (def): The inverse upper half modulus inflated to the actual opposite parabolic.
- `Langlands.LocalFieldData.oppositeParabolicHalfModulus_apply` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_oppositeParabolicHalfModulus` (theorem).
- `Langlands.LocalFieldData.normalizedOppositeParabolicInduced` (def): Normalized parabolic induction `i_(P̄)^G σ` for an actual p-adic field: smooth
  induction by right translation of `δ_P^(-1/2) ⊗ σ`, inflated to the parabolic.
- `Langlands.LocalFieldData.normalizedOppositeParabolicInduced_covariant` (theorem): The covariance `f (p g) = δ_P(m)^(-1/2) σ(m) f(g)` with `m` the Levi part of `p`.
- `Langlands.LocalFieldData.normalizedOppositeParabolicInduced_apply` (theorem): The opposite induced representation acts by right translation.
- `Langlands.LocalFieldData.isSmooth_normalizedOppositeParabolicInduced` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.inflateOppositeCharacter`, `Langlands.GeneralLinear.BlockShape.inflateOppositeCharacter_apply`, `Langlands.GeneralLinear.BlockShape.oppositeInducingRepresentation`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInducedOf`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInducedOf_covariant`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInducedOf_apply`, `Langlands.GeneralLinear.BlockShape.isSmooth_normalizedOppositeInducedOf`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeCompactInducedOf`, `Langlands.GeneralLinear.BlockShape.isSmooth_normalizedOppositeCompactInducedOf`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeCompactInclusionOf`, `Langlands.GeneralLinear.BlockShape.oppositeInducingMap`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInducedOfMap`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInducedOfMap_apply`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInducedOfMap_id`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInducedOfMap_comp`, `Langlands.GeneralLinear.BlockShape.normalizedOppositeInductionFunctorOf`, `Langlands.PadicField.TopologicalData.oppositeParabolicHalfModulus_section`, `Langlands.PadicField.TopologicalData.oppositeParabolicHalfModulus_unipotent`, `Langlands.PadicField.TopologicalData.normalizedOppositeParabolicCompactInduced`, `Langlands.PadicField.TopologicalData.normalizedOppositeParabolicCompactInclusion`, `Langlands.PadicField.TopologicalData.normalizedOppositeParabolicInducedMap`, `Langlands.PadicField.TopologicalData.normalizedOppositeParabolicInducedMap_apply`, `Langlands.PadicField.TopologicalData.normalizedOppositeParabolicInducedMap_id`, `Langlands.PadicField.TopologicalData.normalizedOppositeParabolicInducedMap_comp`, `Langlands.PadicField.TopologicalData.normalizedOppositeParabolicInductionFunctor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

Not ported on purpose: `Langlands.PadicField.canonicalNormalizedOppositeParabolicInduced`, `Langlands.PadicField.canonicalNormalizedOppositeParabolicInductionFunctor`. These are canonical-data wrappers, lemmas comparing two realizations of the same p-adic field, or facts that `Langlands.AllField.LocalField.Foundation` and `Langlands.LocalFactor.LocalAbelian` already provide for every local field; the port works with one supplied realization throughout.
