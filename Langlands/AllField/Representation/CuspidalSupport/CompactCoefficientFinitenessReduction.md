# All-field port of `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction`

`Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Reduction of fixed-level finiteness on `G°` to the corner structure and dimension bound**

Bernstein--Zelevinsky (1976), Theorem 4.14 via 4.16, page 41: the sandwich structure of
compact-open Hecke corners of `G°` (Lemma 4.9) and the dimension bound for simple modules
over sandwich algebras (Lemma 4.10, §4.11) imply that every compact open subgroup of `G°`
has a nonzero fixed vector in only finitely many compact-coefficient classes.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement`
- `Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement`
- `Langlands.AllField.Representation.Smooth.SmallRealizationProof`

## Declarations

- `Langlands.AllField.CuspidalSupport.compactCoefficientFixedLevelFiniteness_of_cornerStructure` (theorem): Bernstein--Zelevinsky (1976), 4.14 via 4.16: the corner structure statement for `G°`
  and the sandwich dimension bound imply fixed-level finiteness of compact-coefficient
  classes on `G°`.

Public declarations of the original that are not re-declared here: `Langlands.CompactCoefficientClass.fixedStratum_mono`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
