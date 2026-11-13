# All-field port of `Langlands.Representation.Smooth.SmallRealizationProof`

`Langlands.AllField.Representation.Smooth.SmallRealizationProof` is the all-field port of the Library module `Langlands.Representation.Smooth.SmallRealizationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Smooth.SmallRealizationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Proof that irreducible smooth complex representations of an actual local-field
general linear group have equivalent realizations in every carrier universe.
The orbit of a nonzero vector is countable and spans, so a basis chosen inside
it is countable and can be reindexed by a type in the prescribed universe.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.AllField.Representation.Smooth.SmallRealizationStatement`

## Declarations

- `Langlands.LocalFieldData.generalLinearSecondCountableTopology` (theorem): The general linear group of an actual nonarchimedean local field, with the topology of a
  supplied realization, is second countable.
- `Langlands.AllField.padicIrreducibleSmoothSmallRealization` (theorem): Irreducible smooth complex representations of an actual local-field general
  linear group have equivalent irreducible smooth realizations in every carrier
  universe.

Public declarations of the original that are not re-declared here: `Langlands.transportRepresentation`, `Langlands.transportRepresentationEquiv`, `Langlands.countable_range_orbit`, `Langlands.exists_irreducible_smoothRep_equiv_of_separable`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
