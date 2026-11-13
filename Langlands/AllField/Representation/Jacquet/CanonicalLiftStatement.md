# All-field port of `Langlands.Representation.Jacquet.CanonicalLiftStatement`

`Langlands.AllField.Representation.Jacquet.CanonicalLiftStatement` is the all-field port of the Library module `Langlands.Representation.Jacquet.CanonicalLiftStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Jacquet.CanonicalLiftStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Core canonical Jacquet lift statements for actual local-field block groups**

These proposition definitions state the representation-theoretic identification
of the generalized kernel and bijectivity of the actual stable-image quotient.
They contain no proofs of these assertions.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitions`

## Declarations

- `Langlands.AllField.Jacquet.BlockStableImageJacquetBijectiveClause` (def): The actual Jacquet quotient is bijective from the all-power stable image
  onto its existing fixed-vector codomain for the unnormalized Levi action.

Public declarations of the original that are not re-declared here: `Langlands.Jacquet.BlockPowerKernelJacquetClause`, `Langlands.Jacquet.BlockCanonicalLiftStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
