# All-field port of `Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessStatement`

`Langlands.AllField.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite twisted coinvariants of irreducible cuspidal Levi representations**

The finite-dimensionality part of the cuspidal-Levi coefficient step in the
proof of Bernstein--Zelevinsky (1976), Theorem 7.12, step (5), printed p.61.
This is a proposition definition, not a proof.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.Whittaker.LeviCuspidalCoinvariantFinitenessStatement` (def): For an irreducible cuspidal smooth complex representation of an actual
  standard product Levi of positive rank, and every locally constant character
  of the product of the blockwise upper-unipotent subgroups, the actual
  character-localized coinvariant quotient is finite-dimensional. The supplied
  topological data determines smoothness, cuspidality and local constancy.
