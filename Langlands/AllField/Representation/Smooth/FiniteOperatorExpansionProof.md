# All-field port of `Langlands.Representation.Smooth.FiniteOperatorExpansionProof`

`Langlands.AllField.Representation.Smooth.FiniteOperatorExpansionProof` is the all-field port of the Library module `Langlands.Representation.Smooth.FiniteOperatorExpansionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Smooth.FiniteOperatorExpansionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the finite operator expansion of a smooth representation of `Fˣ`**

Finitely many vectors separate a finite-dimensional space of operators, so the
intersection of their open stabilizers acts trivially and `b ↦ σ b` is locally
constant. Left multiplication by `σ (ϖ ^ n)` is an injective endomorphism of the
finite-dimensional bounded span, hence surjective, which puts every `σ b` in the
bounded span. The expansion uses the coordinates of a basis of the operator span.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.boundedSpan_eq_span` (theorem): The operators of units with normalized absolute value at most one span the
  whole finite-dimensional operator span.

Public declarations of the original that are not re-declared here: `Langlands.exists_finset_eq_zero_of_apply_eq_zero`, `Langlands.isLocallyConstant_of_finiteDimensional_span`, `Langlands.finiteOperatorExpansion`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
