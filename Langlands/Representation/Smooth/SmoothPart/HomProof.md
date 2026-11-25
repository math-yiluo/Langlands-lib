# Smooth-part linear factorization laws: implemented proof

The closing theorem `Langlands.smoothHomLaws` proves the complete proposition
`Langlands.SmoothHomLawsStatement`, with four component lemmas. The target and
dependencies were checked.

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
closure consists of the following modules:

- `Langlands.Representation.Smooth.SmoothPart.HomDefinitions`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.Definitions`

No project theorem, including the universal-property and functoriality proofs,
is imported. Mathlib supplies intertwiner and subtype extensionality.

## Exact target and provenance

The target is
`Langlands.SmoothHomLawsStatement`, with fingerprint
`ce51e8d44b5d5d84337dc6ef4bc40c9cb4312627694e2c23568769c8a08eb0db`.
The preparation record reports that the target and all three construction
modules had no unavailable dependencies.
The eight target and dependency source files were retained unchanged at
preparation.

The original source context is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, revision June 16, 2019,
Section 1, page 2, first two paragraphs. Literature ID:
`casselman-2019-smooth-representations`; content SHA256:
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The original preparation recorded the Windows locator
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
The same registered original is also at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
That passage defines smoothness via open fixing subgroups and describes the
stable smooth-vector subspace. The four Hom laws are internal consequences
of the imported constructions, not a numbered theorem of Casselman.
The direct proofs justify the target's broader coefficient and group scope.

The preparation environment was
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The preparation record describes machine validation by shared
incremental Lake compilation and exact-target inspection with allowed
assumptions. The proof introduces no placeholders or project axioms.
