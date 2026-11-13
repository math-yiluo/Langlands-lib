# All-field port of `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceProof`

`Langlands.AllField.Representation.Whittaker.JPSBoundedDilationRecurrenceProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the uniform-region recurrence for powers of a bounded coordinate dilation**

The ascending chain of spans of the first powers `σ_i(c ^ j)` in the finite operator
span stabilizes, which gives one length `D` and scalar coefficients `d m j` with
`σ_i(c ^ m) = ∑ j < D, d m j • σ_i(c ^ j)`. For one `f`, the relation for `m = D`
vanishes below a threshold that bounded dilations preserve, so all powers `ρ_i(c ^ m) f`
lie in the span of the first `D` powers plus functions vanishing below it; the finite
span meets the coordinate-vanishing space in a finite-dimensional space with one common
threshold. See the paired Markdown for the route.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement`

## Declarations

- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.normalizedAbs_pow_le_one` (theorem).
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.smallVanishing` (def): Functions vanishing at every torus point whose `i`th coordinate is below `δ`.
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.mem_smallVanishing_iff` (theorem).
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.smallVanishing_anti` (theorem).
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.germMap_eq_zero_of_mem_smallVanishing` (theorem).
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.exists_mem_smallVanishing` (theorem).
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.coordinateRepresentation_mem_smallVanishing` (theorem): Bounded coordinate dilations preserve vanishing below a fixed threshold.
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.exists_threshold_of_finiteDimensional` (theorem): A finite-dimensional space of functions with zero germs has one common threshold.
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.pow_mem_sup` (theorem): A relation among the first powers of a bounded dilation propagates to all its powers,
  modulo functions vanishing below the threshold of that relation.
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.exists_pow_mem_span` (theorem): In a finite operator span, all powers of `σ(c)` lie in the span of the first `D`.
- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceProof.recurrence_of_finiteSpan` (theorem): The uniform-region recurrence for one actual space, coordinate and bounded unit.
- `Langlands.AllField.Whittaker.jpsBoundedDilationRecurrence` (theorem): The uniform-region recurrence for powers of a bounded coordinate dilation.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.JPSBoundedDilationRecurrenceProof.exists_common_threshold`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
