# All-field port of `Langlands.Representation.Whittaker.KirillovStatement`

`Langlands.AllField.Representation.Whittaker.KirillovStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.KirillovStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Whittaker.KirillovStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Kirillov-model prerequisites for the JPSS integral theory**

Proposition targets for the restriction of Whittaker functions to the actual
mirabolic matrices of `GL_{n+1}(F)`. JPSS (1983), Section 2.2, printed page 386;
Bernstein--Zelevinsky (1976), 5.15-5.19, printed pages 49-50.
Neither proposition is asserted to be proved by these definitions.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.WhittakerTypeKirillovStatement` (def): JPSS (2.2): for an admissible representation of finite type whose space of
  Whittaker functionals is one-dimensional, every smooth left `(N, θ)`-covariant
  function on the mirabolic subgroup with compact support modulo `N` is the
  restriction of a Whittaker function.

  The upper-unitriangular, mirabolic, covariance, smoothness and support
  conditions are spelled out on actual matrices; nothing is parameterized by an
  arbitrary predicate.

Public declarations of the original that are not re-declared here: `Langlands.SupercuspidalKirillovStatement`, `Langlands.KirillovPrerequisitesStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
