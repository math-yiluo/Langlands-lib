# Smooth-part linear factorization laws: implemented proof

The closing theorem `Langlands.smoothHomLaws` proves the complete proposition
`Langlands.SmoothHomLawsStatement`. Worker 0 authored the proof and its four
component lemmas; Worker 52 checked the target and dependencies, retained the
proof terms, and prepared this documented submission.

The artifact IDs, environment, commits and acceptance accounts below are
retained historical Test 2 preparation records. The ten-contribution export
checked on October 23, 2026 does not cover this Hom statement or proof, so this
status correction supplies no independent acceptance or non-acceptance verdict
for either. Source-level implementation is distinct from that historical
verification question; see [HomStatement](HomStatement.md).

The component proofs are:

| Lemma | Implemented argument |
| --- | --- |
| `smoothHomEquiv_apply` | The forward map is `smoothLift`; forgetting the smooth-vector membership proof leaves `f v`. The proof is `rfl`. |
| `smoothHomEquiv_symm_apply` | The inverse composes with `smoothInclusion`, so its value is the underlying value of `f v`. The proof is `rfl`. |
| `smoothHomEquiv_postcomp` | `ext v` reduces intertwiner equality to pointwise equality. Both sides have underlying value `g (f v)`; `rfl` closes the goal. |
| `smoothHomEquiv_precomp` | `ext v` reduces the equation to values on the smooth source. Both sides have underlying value `f (g v)`; `rfl` closes the goal. |

Subtype membership proofs do not change these values. The extensionality
steps and definitional equality account for the subtype proof fields.
All four helpers remain in this module.

The closing theorem introduces the topological-group instance quantified by
the target, then supplies the four component lemmas. All original ring, group,
module, and five independent universes `uR uG uV uW uU` are retained.
The coefficients form an arbitrary commutative ring. Smoothness of the
sources is supplied inside the clauses; precomposition requires both sources
to be smooth. The `omit [IsTopologicalGroup G]` command keeps that assumption
inside the target rather than adding it as a parameter of the closing theorem.
No smoothness of the target, compactness, admissibility, finite dimension,
Noetherian hypothesis, or topology on the modules is added.

Only [HomStatement](HomStatement.md) is imported. Its full project construction
closure consists of the following modules, identified in the original
preparation record as accepted and published version-1 artifacts:

| Module | Artifact |
| --- | --- |
| `Langlands.Representation.Smooth.SmoothPart.HomDefinitions` | `e17aa7ac-f4d5-4ac3-84f2-b7c706899ce0` |
| `Langlands.Representation.Smooth.SmoothPart.Definitions` | `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` |
| `Langlands.Representation.Smooth.Definitions` | `665022df-625b-44ae-9dbd-425f6e266bab` |

No project theorem, including the universal-property and functoriality proofs,
is imported. Mathlib supplies intertwiner and subtype extensionality.

## Exact target and provenance

The original preparation record identifies the accepted target as
`b3eb0c30-50c1-4582-9ac6-ba233f5266d7` version 1,
`Langlands.SmoothHomLawsStatement`, with fingerprint
`ce51e8d44b5d5d84337dc6ef4bc40c9cb4312627694e2c23568769c8a08eb0db`. It was published at
`9db46907db3181b0c1dfd287b8ab2f1f02054cab`; its independent semantic receipt is
`1c63dd75cad24a3ab0941610d6138230`. That record reports fresh fetches confirming
the target and all three construction artifacts were current at Test 2 commit
`5bc58c2525e0499012801c80f17b6a9c04d57263`, with no unavailable dependencies.
The eight target and dependency source files were retained unchanged at that
preparation checkpoint.

The original source context is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, revision June 16, 2019,
Section 1, page 2, first two paragraphs. Literature ID:
`casselman-2019-smooth-representations`; content SHA256:
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The original preparation recorded the historical Windows locator
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`,
which is not a current path. The same registered original is readable in this
pilot at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
That passage defines smoothness via open fixing subgroups and describes the
stable smooth-vector subspace. The four Hom laws are internal consequences
of the imported constructions, not a numbered theorem of Casselman.
The direct proofs justify the target's broader coefficient and group scope.

The original preparation environment was
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The original preparation record describes machine validation by shared
incremental Lake compilation and exact-target inspection with allowed
assumptions. The supplied export contains no Hom validation, approval or
publication record, so no historical outcome of that workflow is asserted
here. The proof introduces no placeholders or project axioms. Source presence
and compilation alone do not establish independent acceptance or publication.
