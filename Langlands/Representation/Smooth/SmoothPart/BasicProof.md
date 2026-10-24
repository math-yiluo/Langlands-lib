# Basic properties of the smooth part: implemented proof

The original proof was independently accepted and published in Test 2 on
October 15, 2026. The exact validation, independent approval and publication
records, verified on October 23, are in
[BasicStatement](BasicStatement.md#verified-historical-status). The preparation
accounts, artifact IDs, environment and commits below are historical Test 2
records. They are distinct from the later pilot documentation correction.

Worker 0 supplied the complete implementation; Worker 24 checked it against
the accepted dependencies and prepared this pair for independent review.
The closing theorem `Langlands.smoothPartBasic` proves precisely
`SmoothPartBasicStatement`, importing the accepted statement
`7101568f-3e71-4b9d-b1c5-f35546e0e8dd` version 1,
published at commit `6c1028baa3f29e21f18dd147d07f4b7873a88b8c`, with
receipt `a2c4fec7-eaaa-4396-889d-edf61fcd5156`.
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

This is an internal proof from the accepted constructions and Mathlib's
submodule and subtype interfaces. The mathematical provenance of those
constructions is documented in [the target](BasicStatement.md) and
[definitions](Definitions.md). The proof imports no external source theorem.

The transitive construction dependencies are smooth-part definitions
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` version 1 and foundational smoothness
definitions `665022df-625b-44ae-9dbd-425f6e266bab` version 1. No other project
proof is imported. The original preparation environment was
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1, Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Before the original submission, Worker 24 fetched the full final reviews and confirmed that
the target and both definition pairs were accepted, published, and current at
Test 2 commit `e733f3dda0099f9951b5c427fc3783c2ebdf3f45`, without unavailable
dependencies or changed files. All six local dependency files matched their
effective published hashes at that preparation checkpoint.

The original pair reused Worker 0's public proof draft for task
`3b5e1c81-ba5a-4300-8ff6-27a11ca276e7`, revision 1, draft content key
`87ef6e6bfec88b1d037a85af05789cd1e532e77ae0fbb4c19795947deabc472a`.
The mathematical Lean implementation was unchanged from that draft. All
component lemmas remain in this one coherent proof module. The original proof
task bound the exact target version, environment, module, and closing theorem.
Native compilation during that preparation checked elaboration only. The
original acceptance and publication came from the separate registered proof
validation, independent approval and Test 2 publication recorded in
[BasicStatement](BasicStatement.md#verified-historical-status). Neither those
historical records nor source compilation accepts this later Markdown
correction.
