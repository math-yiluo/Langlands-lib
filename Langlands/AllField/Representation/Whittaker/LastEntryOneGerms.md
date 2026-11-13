# All-field port of `Langlands.Representation.Whittaker.LastEntryOneGerms`

`Langlands.AllField.Representation.Whittaker.LastEntryOneGerms` is the all-field port of the Library module `Langlands.Representation.Whittaker.LastEntryOneGerms`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.LastEntryOneGerms` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Root coefficient maps into the actual coordinate germs**

The general Jacquet factorization below has an explicit kernel-vanishing
premise. The final Whittaker specialization discharges it using the published
kernel theorem and obtains finite operator spans from the published
Jacquet-center theorem.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.JacquetCenterSpanProof`
- `Langlands.AllField.Representation.Whittaker.CoordinateJacquetKernelProof`
- `Langlands.AllField.Representation.Whittaker.JPSFunctionSpace`
- `Langlands.AllField.Representation.Whittaker.LastEntryOneAdapters`
- `Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof`

## Declarations

- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientToSpace` (def): The actual coefficient map corestricted to its invariant image.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientToSpace_surjective` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.rootGermMap` (def): The canonical surjection from the original carrier to a coordinate germ.
- `Langlands.AllField.WhittakerLastEntryOne.rootGermMap_surjective` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.rootGermMap_eq_zero_iff` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.rootGermMap_coordinate` (theorem): Pulling back along the coordinate embedding gives the literal dilation action.
- `Langlands.AllField.WhittakerLastEntryOne.rootLift_coordinateEmbedding` (theorem): A single root-coordinate dilation scales exactly the initial diagonal block.
- `Langlands.AllField.WhittakerLastEntryOne.coordinateBlockScalars` (def): The scalar tuple `(b,1)` in that actual product Levi.
- `Langlands.AllField.WhittakerLastEntryOne.torus_rootLift_coordinateEmbedding` (theorem): The actual diagonal root lift equals the embedded two-block scalar.
- `Langlands.AllField.WhittakerLastEntryOne.jacquetToRootGerm` (def): The actual Jacquet quotient maps to coordinate germs once its kernel vanishes.
- `Langlands.AllField.WhittakerLastEntryOne.jacquetToRootGerm_mk` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.jacquetToRootGerm_surjective` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.coordinateJacquetRepresentation` (def): The unnormalized actual two-block Jacquet action restricted to `(b,1)`.
- `Langlands.AllField.WhittakerLastEntryOne.coordinateJacquetRepresentation_mk` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.coordinateJacquetToRootGerm` (def): The actual Jacquet-to-germ quotient map is equivariant for coordinate dilation.
- `Langlands.AllField.WhittakerLastEntryOne.coordinateJacquetToRootGerm_surjective` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace_finiteCoordinateOperatorSpan` (theorem): All-block-scalar finite span descends to the actual coordinate-germ action,
  provided the actual Jacquet kernel has the stated vanishing property.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace_isLocallyConstantSpace` (theorem): The source's separate local-constancy predicate holds for the actual
  root coefficient image, without a topology on the original carrier.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace_hasCoordinateUpperSupport_of_statement` (theorem): The raw upper-support adapter implies the published coordinatewise support
  predicate, with the same bound uniform in every other coordinate.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace_hasCoordinateUpperSupport` (theorem): Published simple-root support gives the JPS upper-support hypothesis for
  the actual root coefficient image of every smooth Whittaker functional.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficient_kernel` (theorem): The published full-diagonal kernel theorem supplies exactly the actual
  root-coordinate vanishing premise used by the Jacquet-to-germ map.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace_finiteOperatorSpans` (theorem): The published kernel and all-block-scalar span proofs imply all
  finite coordinate operator spans for the actual root coefficient image.

Public declarations of the original that are not re-declared here: `Langlands.WhittakerLastEntryOne.operatorSpan_finite_of_surjective`, `Langlands.WhittakerLastEntryOne.operatorSpan_finite_comp`, `Langlands.WhittakerLastEntryOne.coordinateBlock`, `Langlands.WhittakerLastEntryOne.rootCoefficientSpace_isSmoothSpace`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
