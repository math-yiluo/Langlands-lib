# All-field port of `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement`

`Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Fixed-level finiteness of compact-coefficient classes on `G°`**

Bernstein--Zelevinsky (1976), Theorem 4.14, page 41, in its compact-open form.
This is a proposition definition, not a proof.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit`

## Declarations

- `Langlands.AllField.CuspidalSupport.CompactCoefficientFixedLevelFinitenessTheorem` (def): For every positive-rank product Levi over an actual nonarchimedean local field, each
  compact open subgroup of its determinant-unit subgroup `G°` has a nonzero fixed
  vector in only finitely many isomorphism classes of irreducible smooth complex
  representations of `G°` with compact smooth-dual coefficients.
