# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankSpecializationInputs`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankSpecializationInputs` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankSpecializationInputs`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankSpecializationInputs` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Supplied-topology inputs for the unequal-rank finite-length assembly.

## Proof route

In the original, `finiteLength_of_whittakerType` calls the p-adic theorem
`glAdmissibleFiniteLength p F`, which is stated for the canonical topology. It first
rewrites the smoothness hypothesis `hπ.1` from the supplied topology to the canonical
topology, using `T.topology_eq_canonicalModule`. In the port, `glAdmissibleFiniteLength`
(from the port of `Langlands.Representation.Classification.FiniteLengthProof`) is stated for
arbitrary data `T : LocalFieldData F`. So `finiteLength_of_whittakerType` calls
`glAdmissibleFiniteLength F T` with `hπ.1` as it is, without rewriting. The other
declarations keep the proofs of the original.

## Imports from the port

- `Langlands.AllField.Representation.Classification.FiniteLengthProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicFunctionalTransfer`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.finiteLength_of_whittakerType` (theorem): Whittaker type supplies finite length over the original general linear
  group, for the topology actually supplied by `T`.
- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.mirabolicFunctionalEquivOfWhittakerType` (def): Choose the one-dimensional functional-space equivalence on the actual
  mirabolic restriction from the full Whittaker-type hypothesis.
- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.mirabolic_smooth_and_character_locallyConstant_of_whittakerType` (theorem): The actual mirabolic restriction is smooth, and its transported
  functional character is locally constant.
- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.character_locallyConstant_of_whittakerType` (theorem): The original general linear character is locally constant as well,
  including the inverse-standard character used by the smaller factor.
- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.generalLinear_compactOpen_cofinal` (theorem): Every open subgroup of the smaller general linear group contains a
  compact open subgroup for the topology supplied by `T`.
