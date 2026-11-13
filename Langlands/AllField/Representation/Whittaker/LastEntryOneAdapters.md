# All-field port of `Langlands.Representation.Whittaker.LastEntryOneAdapters`

`Langlands.AllField.Representation.Whittaker.LastEntryOneAdapters` is the all-field port of the Library module `Langlands.Representation.Whittaker.LastEntryOneAdapters`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Whittaker.LastEntryOneAdapters` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Coefficient and support adapters for the last-entry-one expansion**

The upper-support adapter explicitly assumes the published support proposition.
These helpers do not establish the analytic expansion.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Group.GL.UnramifiedCharacter`
- `Langlands.AllField.HarmonicAnalysis.Conductor`
- `Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`
- `Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof`
- `Langlands.AllField.Representation.Whittaker.LastEntryOneAssembly`
- `Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportStatement`

## Declarations

- `Langlands.AllField.WhittakerLastEntryOne.rootLiftHom` (def): The cumulative-product section as an actual group homomorphism.
- `Langlands.AllField.WhittakerLastEntryOne.continuous_rootLiftHom` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientMap` (def): Restriction of an actual matrix coefficient to the simple-root torus,
  with its intertwining law for right translation.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace` (def): The actual translation-stable space of root-coordinate coefficients.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientMap_apply` (theorem).
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace_locallyConstant` (theorem): Every function in the actual coefficient image is locally constant.
  This uses smoothness of the orbit map, without any topology on the carrier.
- `Langlands.AllField.WhittakerLastEntryOne.upper_support_of_statement` (theorem): The supplied-topology support proposition implies the raw coefficient bound
  needed by the root-coordinate function space, with one bound for every root.
- `Langlands.AllField.WhittakerLastEntryOne.rootCoefficientSpace_upper_support` (theorem): The support proposition bounds all coordinates of each function in the
  actual root coefficient image, uniformly in the other coordinates.

Public declarations of the original that are not re-declared here: `Langlands.WhittakerLastEntryOne.torus_eq_diagonalUnits`, `Langlands.WhittakerLastEntryOne.continuous_torus`, `Langlands.WhittakerLastEntryOne.rootCoefficientSpace_smooth`, `Langlands.WhittakerLastEntryOne.model_finite`, `Langlands.WhittakerLastEntryOne.model_admissible`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
