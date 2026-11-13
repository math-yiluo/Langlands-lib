# All-field port of `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`

`Langlands.AllField.HarmonicAnalysis.PadicAdditiveConductorProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Additive-conductor scaling and the actual integer-ring annihilator.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.Conductor`

## Declarations

- `Langlands.LocalFieldData.mem_additiveLattice_iff_exists_integer` (theorem): Membership in the valuation lattice is membership in the actual fractional ideal.
- `Langlands.LocalFieldData.mul_mem_additiveLattice_iff` (theorem): Multiplication transports the actual valuation lattices with the normalized order.
- `Langlands.LocalFieldData.integer_annihilator_iff_mem_additiveLattice` (theorem): The annihilator of the actual integer ring is the conductor lattice.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.forall_integers_uniformizer_mul_iff`, `Langlands.PadicField.TopologicalData.triviality_mulShift_iff`, `Langlands.PadicField.TopologicalData.isGreatest_fractionalIdeal_triviality`, `Langlands.HarmonicAnalysis.padicAdditiveConductor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
