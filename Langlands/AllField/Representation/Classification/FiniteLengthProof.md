# All-field port of `Langlands.Representation.Classification.FiniteLengthProof`

`Langlands.AllField.Representation.Classification.FiniteLengthProof` is the all-field port of the Library module `Langlands.Representation.Classification.FiniteLengthProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Classification.FiniteLengthProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Finite length of admissible finitely generated GL representations.
The proof inducts on the semisimple rank of standard product Levis.

## Proof route

`Langlands.AllField.glAdmissibleFiniteLength` proves the ported
`GLAdmissibleFiniteLengthStatement` for the topology of the supplied data `T` directly:
it applies the ported normalized-Jacquet finite-length result for `T` to the single-block
shape. The original proves the canonical-topology statement and rewrites with
`PadicField.canonicalTopologicalData_topology`; that step is no longer needed.

## Imports from the port

- `Langlands.AllField.Representation.Classification.FiniteLengthStatement`
- `Langlands.AllField.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof`
- `Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalFiniteLengthProof`
- `Langlands.AllField.Representation.CuspidalSupport.RefinedJacquetLengthProof`
- `Langlands.AllField.Representation.Induction.SingleBlock`
- `Langlands.AllField.Representation.Parabolic.FlattenedJacquetQuotientProof`
- `Langlands.AllField.Representation.Parabolic.JacquetFiniteGenerationProof`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`

## Declarations

- `Langlands.AllField.FiniteLengthAssembly.normalizedJacquet_eq_twist` (theorem): The two published presentations of the normalized product-Levi action agree.
- `Langlands.AllField.FiniteLengthAssembly.isAdmissible_normalizedJacquet` (theorem): Apply the published admissibility theorem to the standard Jacquet API.
- `Langlands.AllField.FiniteLengthAssembly.isAdmissible_levi_subrepresentation` (theorem): Invariant subspaces inherit admissibility through their actual inclusion.
- `Langlands.AllField.FiniteLengthAssembly.refinement_measure_lt` (theorem): Proper refinement strictly decreases the natural-number induction measure.
- `Langlands.AllField.FiniteLengthAssembly.refinedJacquetMap_surjective` (theorem): The actual normalized refined Jacquet map preserves surjectivity.
- `Langlands.AllField.FiniteLengthAssembly.finiteLength_of_refinedJacquet` (theorem): The decomposition and detection theorems reduce finite length to the
  proper refined Jacquet modules.
- `Langlands.AllField.FiniteLengthAssembly.finiteLength_normalizedJacquet_of_refinements` (theorem): For a standard Jacquet module, the published admissibility and
  finite-generation results discharge both inputs of the decomposition step.
- `Langlands.AllField.FiniteLengthAssembly.singleBlockJacquetInclusion` (def): In one block the quotient map is equivariant for the original Levi action.
- `Langlands.AllField.FiniteLengthAssembly.singleBlockJacquetInclusion_injective` (theorem).
- `Langlands.AllField.FiniteLengthAssembly.finiteLength_of_singleBlockJacquet` (theorem): Finite length of a one-block normalized Jacquet module gives finite length
  of the original representation, with no smoothness assumption needed here.
- `Langlands.AllField.Parabolic.normalizedJacquetFiniteLength` (theorem): Every standard normalized Jacquet module of an admissible finitely generated
  ambient GL representation has finite length over the actual product-Levi group
  algebra, including rank zero and arbitrary independent carrier universes.
- `Langlands.AllField.glAdmissibleFiniteLength` (theorem): An admissible finitely generated representation of positive-rank GL over
  an actual nonarchimedean local field has finite group-algebra length.

Public declarations of the original that are not re-declared here: `Langlands.FiniteLengthAssembly.length_comp_surjective`, `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff`, `Langlands.FiniteLengthAssembly.finite_of_surjective`, `Langlands.FiniteLengthAssembly.finiteLength_of_surjective`, `Langlands.FiniteLengthAssembly.finiteLength_of_injective`, `Langlands.FiniteLengthAssembly.complementaryProjection`, `Langlands.FiniteLengthAssembly.complementaryProjection_surjective`, `Langlands.FiniteLengthAssembly.finite_summand`, `Langlands.FiniteLengthAssembly.length_eq_add_of_complement`, `Langlands.FiniteLengthAssembly.finiteLength_of_complement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
