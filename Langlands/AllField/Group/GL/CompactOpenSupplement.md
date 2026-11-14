# All-field supplement to `Langlands.AllField.Group.GL.CompactOpen`

`Langlands.AllField.Group.GL.CompactOpenSupplement` supplements the Library module `Langlands.AllField.Group.GL.CompactOpen`, the existing all-field port of `Langlands.Group.GL.CompactOpen`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Group.GL.CompactOpen` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Group.GL.CompactOpen` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact open subgroups for actual p-adic matrix groups**

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpen`
- `Langlands.AllField.Group.GL.PadicOppositeBlocks`

## Declarations

- `Langlands.LocalFieldData.parabolicNonarchimedean` (theorem): The actual upper block parabolic is nonarchimedean in the supplied topology.
- `Langlands.LocalFieldData.unipotentRadicalNonarchimedean` (theorem): The actual block unipotent radical is nonarchimedean in the supplied topology.
- `Langlands.LocalFieldData.generalLinearCompactOpen` (def): Choose an actual compact open subgroup inside a GL identity neighborhood.
- `Langlands.LocalFieldData.parabolicCompactOpen` (def): Choose a compact open subgroup inside an identity neighborhood of the upper block parabolic.
- `Langlands.LocalFieldData.unipotentRadicalCompactOpen` (def): Choose a compact open subgroup inside an identity neighborhood of the block unipotent radical.

Declarations of the original re-declared by `Langlands.AllField.Group.GL.CompactOpen` and therefore not here: `Langlands.PadicField.TopologicalData.generalLinearNonarchimedean`, `Langlands.PadicField.TopologicalData.leviNonarchimedean`, `Langlands.PadicField.TopologicalData.upperUnipotentNonarchimedean`, `Langlands.PadicField.TopologicalData.upperUnipotentCompactOpen`.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.oppositeParabolicNonarchimedean`, `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalNonarchimedean`, `Langlands.PadicField.TopologicalData.oppositeParabolicCompactOpen`, `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalCompactOpen`, `Langlands.PadicField.TopologicalData.leviCompactOpen`, `Langlands.PadicField.canonicalParabolicNonarchimedean`, `Langlands.PadicField.canonicalParabolicCompactOpen`, `Langlands.PadicField.canonicalOppositeParabolicNonarchimedean`, `Langlands.PadicField.canonicalOppositeParabolicCompactOpen`, `Langlands.PadicField.canonicalUnipotentRadicalNonarchimedean`, `Langlands.PadicField.canonicalUnipotentRadicalCompactOpen`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalNonarchimedean`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalCompactOpen`, `Langlands.PadicField.canonicalLeviNonarchimedean`, `Langlands.PadicField.canonicalLeviCompactOpen`, `Langlands.PadicField.canonicalUpperUnipotentNonarchimedean`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

Not ported on purpose: `Langlands.PadicField.canonicalGeneralLinearNonarchimedean`, `Langlands.PadicField.canonicalGeneralLinearCompactOpen`, `Langlands.PadicField.canonicalUpperUnipotentCompactOpen`. These are canonical-data wrappers, lemmas comparing two realizations of the same p-adic field, or facts that `Langlands.AllField.LocalField.Foundation` and `Langlands.LocalFactor.LocalAbelian` already provide for every local field; the port works with one supplied realization throughout.
