# All-field port of `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`

`Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

The original uses the canonical normed-field structure `F.canonicalNormedField` of the p-adic field, and transports a supplied realization to it (`topology_eq_canonical…`). The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`. The transport is then unnecessary and is omitted.

Source: the original module `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Residue-normalized scalar Haar scaling**

Intrinsic topology and regularity lemmas for a supplied local-field realization,
followed by the scalar pushforward formula for every additive Haar measure.

## Proof route

The original proves six topological facts about the supplied p-adic realization in this
module (σ-compactness, second countability, pseudometrizability, compactness and openness
of the integer ring, regularity of additive Haar measures). For a general local field these
are `Langlands.LocalFieldData.sigmaCompactSpace`, `secondCountableTopology`,
`pseudoMetrizableSpace`, `isCompact_integers`, `isOpen_integers` and `haarMeasure_regular`
in `Langlands.AllField.LocalField.Foundation`, which the ported proofs use instead.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicHaarScalingStatement`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling` (theorem): Scalar pushforward of any additive Haar measure, using the supplied
  residue-normalized absolute value and deriving regularity intrinsically.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.sigmaCompactSpace`, `Langlands.PadicField.TopologicalData.secondCountableTopology`, `Langlands.PadicField.TopologicalData.isCompact_integers`, `Langlands.PadicField.TopologicalData.isOpen_integers`, `Langlands.PadicField.TopologicalData.pseudoMetrizableSpace`, `Langlands.PadicField.TopologicalData.haarMeasure_regular`, `Langlands.HarmonicAnalysis.padicScalarHaarScalingStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
