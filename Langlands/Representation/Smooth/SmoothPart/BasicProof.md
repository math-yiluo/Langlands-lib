# Basic properties of the smooth part: implemented proof

The implementation was checked against its dependencies.
The closing theorem `Langlands.smoothPartBasic` proves precisely
`SmoothPartBasicStatement`, importing the statement module
`Langlands.Representation.Smooth.SmoothPart.BasicStatement`.
Its exact target fingerprint is
`3d50174d1c57c23714f56200cd4a600c23d2366a0a9816143290416a74e005f7`.

The ring, group, and module have independent universes. The ambient assumptions
are `CommRing R`, `Group G`, `TopologicalSpace G`, `AddCommGroup V`, and
`Module R V`. There is no topology on the module or finiteness hypothesis.

The zero, addition, and scalar lemmas extract the submodule construction fields.
`mem_smoothVectors_iff` is definitional. If every vector is smooth, the submodule
contains the top submodule; conversely, equality with top makes each vector a
member. This proves `isSmooth_iff_smoothVectors_eq_top`.

For a topological group, `isSmoothVector_apply` extracts the action-invariance
field of `smoothSubrepresentation`. Inclusion is definitionally the subtype
map, so its formula is reflexive and its injectivity is `Subtype.val_injective`.
To prove `isSmooth_smoothPart`, take each subtype vector's fixing open subgroup.
The same subgroup fixes it in the restricted representation: subtype
extensionality reduces this to the original fixing equation.

The closing theorem packages exactly these clauses and introduces the
topological-group instance at its explicit position in the proposition. It
has no additional ambient topological-group assumption.

This is an internal proof from the constructions and Mathlib's
submodule and subtype interfaces. The mathematical provenance of those
constructions is documented in [the target](BasicStatement.md) and
[definitions](Definitions.md). The proof imports no external source theorem.

The transitive construction dependencies are the smooth-part definitions
`Langlands.Representation.Smooth.SmoothPart.Definitions` and the foundational
smoothness definitions `Langlands.Representation.Smooth.Definitions`. No other
project proof is imported. The preparation environment was
Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The target and both definition modules were checked to have no unavailable
dependencies or changed files. All six local dependency files matched their
recorded hashes.

All component lemmas remain in this one coherent proof module. Native
compilation checked elaboration. The proof's validation against the exact
target is recorded in [BasicStatement](BasicStatement.md#checks).
