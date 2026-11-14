# All-field supplement to `Langlands.AllField.Group.GL.Padic`

`Langlands.AllField.Group.GL.PadicSupplement` supplements the Library module `Langlands.AllField.Group.GL.Padic`, the existing all-field port of `Langlands.Group.GL.Padic`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Group.GL.Padic` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Group.GL.Padic` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**General linear groups over every finite p-adic extension**

These explicit structures install the topology of a supplied `TopologicalData`
on the actual matrix unit group. The canonical specialization needs only the
algebraic `PadicField`.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

The port declares no public declarations.

Declarations of the original re-declared by `Langlands.AllField.Group.GL.Padic` and therefore not here: `Langlands.PadicField.TopologicalData.generalLinearTopology`, `Langlands.PadicField.TopologicalData.generalLinearTopologicalGroup`, `Langlands.PadicField.TopologicalData.generalLinearT2Space`, `Langlands.PadicField.TopologicalData.generalLinearLocallyCompactSpace`, `Langlands.PadicField.TopologicalData.generalLinearDeterminant`.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.generalLinearScalar`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

Not ported on purpose: `Langlands.PadicField.canonicalGeneralLinearTopology`, `Langlands.PadicField.canonicalGeneralLinearTopologicalGroup`, `Langlands.PadicField.canonicalGeneralLinearT2Space`, `Langlands.PadicField.canonicalGeneralLinearLocallyCompactSpace`. These are canonical-data wrappers, lemmas comparing two realizations of the same p-adic field, or facts that `Langlands.AllField.LocalField.Foundation` and `Langlands.LocalFactor.LocalAbelian` already provide for every local field; the port works with one supplied realization throughout.
