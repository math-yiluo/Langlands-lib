# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The unequal-rank rational functional equation at block zero**

This internal prerequisite isolates the block-zero part of JPSS Theorem 2.7.
The universal existence proposition retains the full Whittaker-type scope.
It is a statement, not a proof of existence.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankBlockZeroGammaExistenceStatement` (def): Existence of one nonzero rational gamma function at block zero, with the
  field, topology, measures, Whittaker-type hypotheses and nonzero specified
  functionals of `UnequalRankFunctionalEquationStatement`. The function `G` is
  chosen before all coefficient vectors. Extending the irreducible-generic
  uniqueness argument of JPSS Section 2.11 to this full scope remains a proof
  obligation; no such argument is assumed here.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankBlockZeroGammaEquation`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
