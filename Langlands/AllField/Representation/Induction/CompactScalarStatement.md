# All-field port of `Langlands.Representation.Induction.CompactScalarStatement`

`Langlands.AllField.Representation.Induction.CompactScalarStatement` is the all-field port of the Library module `Langlands.Representation.Induction.CompactScalarStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Induction.CompactScalarStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The scalar compact-picture integral for standard GL parabolics**

This proposition specifies a compact open Iwasawa subgroup and one Haar
probability measure whose integral is invariant under every ambient right
translation of each locally constant full-modulus-covariant scalar function.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`

## Declarations

- `Langlands.AllField.GLParabolicCompactScalarIntegralStatement` (def): Existence of the right-invariant scalar compact-picture integral for every
  standard block parabolic of a positive-rank general linear group.
