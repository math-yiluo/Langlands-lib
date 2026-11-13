# All-field port of `Langlands.Representation.Whittaker.AsymptoticStatement`

`Langlands.AllField.Representation.Whittaker.AsymptoticStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.AsymptoticStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Whittaker.AsymptoticStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Gauge bounds and torus expansions of Whittaker functions**

Proposition targets for JPSS (1983), Section 2.5, printed pages 388-389,
which recalls JPS, *Automorphic forms on GL(3) I* (1979), Section 2,
Proposition (2.2), Remark (2.2.5) and the gauges of (2.3). The diagonal
torus is parameterized by families of units and its simple-root coordinates are
`a i / a (i + 1)`. None of the propositions is asserted to be proved.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.WhittakerTypeAsymptoticStatement` (def): JPS (1979), Proposition (2.2) with Remark (2.2.5), for the Whittaker
  functions of a representation of Whittaker type in the sense of JPSS (2.1):
  there is a finite set `X` of finite functions on the diagonal torus, depending
  only on the representation, such that on the torus every Whittaker function is
  `∑ χ ∈ X, φ_χ (α a) * χ a` with Schwartz--Bruhat functions `φ_χ`.

  A finite function is a continuous function whose translates span a
  finite-dimensional space.

Public declarations of the original that are not re-declared here: `Langlands.WhittakerGaugeStatement`, `Langlands.GenericWhittakerAsymptoticStatement`, `Langlands.WhittakerAsymptoticPrerequisitesStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
