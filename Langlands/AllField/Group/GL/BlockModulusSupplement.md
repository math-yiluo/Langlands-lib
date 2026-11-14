# All-field supplement to `Langlands.AllField.Group.GL.BlockModulus`

`Langlands.AllField.Group.GL.BlockModulusSupplement` supplements the Library module `Langlands.AllField.Group.GL.BlockModulus`, the existing all-field port of `Langlands.Group.GL.BlockModulus`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Group.GL.BlockModulus` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Group.GL.BlockModulus` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Explicit positive block modulus characters**

For the standard upper block parabolic the factor contributed by blocks `i < j`
is `|det m_i| ^ n_j / |det m_j| ^ n_i`. The character is built from these actual
determinants. Its interpretation as Haar scaling is a separate theorem.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Group.GL.PadicBlocksSupplement`

## Declarations

- `Langlands.LocalFieldData.continuous_leviModulus` (theorem): Continuity for the product of the actual block determinant norms.
- `Langlands.LocalFieldData.leviModulus_scalar` (theorem): Every pair of block contributions cancels on an ambient scalar matrix.
- `Langlands.LocalFieldData.leviHalfModulus_sq` (theorem).

Declarations of the original re-declared by `Langlands.AllField.Group.GL.BlockModulus` and therefore not here: `Langlands.PadicField.TopologicalData.blockDeterminantNorm`, `Langlands.PadicField.TopologicalData.blockDeterminantNorm_apply`, `Langlands.PadicField.TopologicalData.leviModulus`, `Langlands.PadicField.TopologicalData.leviModulus_apply`, `Langlands.PadicField.TopologicalData.normOneLevi`, `Langlands.PadicField.TopologicalData.mem_normOneLevi`, `Langlands.PadicField.TopologicalData.normOneLevi_le_ker_leviModulus`, `Langlands.PadicField.TopologicalData.isOpen_normOneLevi`, `Langlands.PadicField.TopologicalData.isOpen_ker_leviModulus`, `Langlands.PadicField.TopologicalData.leviHalfModulus`, `Langlands.PadicField.TopologicalData.leviHalfModulus_apply`, `Langlands.PadicField.TopologicalData.leviHalfModulus_eq_one`, `Langlands.PadicField.TopologicalData.isOpen_ker_leviHalfModulus`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus_apply`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus_section`, `Langlands.PadicField.TopologicalData.isOpen_ker_parabolicHalfModulus`.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.parabolicModulus`, `Langlands.PadicField.TopologicalData.parabolicModulus_apply`, `Langlands.PadicField.TopologicalData.parabolicModulus_section`, `Langlands.PadicField.TopologicalData.parabolicModulus_unipotent`, `Langlands.PadicField.TopologicalData.isOpen_ker_parabolicModulus`, `Langlands.PadicField.TopologicalData.continuous_parabolicModulus`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus_unipotent`, `Langlands.PadicField.TopologicalData.inverseHalf_leviModulus`, `Langlands.PadicField.TopologicalData.parabolicModulus_eq`, `Langlands.PadicField.canonicalLeviModulus`, `Langlands.PadicField.canonicalParabolicModulus`, `Langlands.PadicField.canonicalLeviHalfModulus`, `Langlands.PadicField.canonicalParabolicHalfModulus`, `Langlands.PadicField.isOpen_ker_canonicalLeviModulus`, `Langlands.PadicField.isOpen_ker_canonicalParabolicModulus`, `Langlands.PadicField.isOpen_ker_canonicalLeviHalfModulus`, `Langlands.PadicField.isOpen_ker_canonicalParabolicHalfModulus`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

Not ported on purpose: `Langlands.PadicField.TopologicalData.leviModulus_eq`, `Langlands.PadicField.TopologicalData.leviHalfModulus_eq`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus_eq`. These are canonical-data wrappers, lemmas comparing two realizations of the same p-adic field, or facts that `Langlands.AllField.LocalField.Foundation` and `Langlands.LocalFactor.LocalAbelian` already provide for every local field; the port works with one supplied realization throughout.
