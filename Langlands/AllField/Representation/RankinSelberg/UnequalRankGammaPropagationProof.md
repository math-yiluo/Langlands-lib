# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankGammaPropagationProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankGammaPropagationProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankGammaPropagationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankGammaPropagationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Same-multiplier propagation from the published paired transfer and
adjacent-span proofs, retaining the actual coefficient-model integrals.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockSpanProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankComplementaryTransferProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankGammaPropagationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.unequalRankGammaPropagation` (theorem): The literal block-zero gamma equation propagates to all complementary
  blocks with the same supplied rational multiplier and the same measures.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.unequalRankGammaEquation_of_pairedTransfer`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
