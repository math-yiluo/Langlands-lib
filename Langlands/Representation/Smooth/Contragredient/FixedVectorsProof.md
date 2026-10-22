# Fixed smooth functionals: implemented proof

`Langlands.smoothDualFixedVectors` proves all four clauses of the published
`Langlands.SmoothDualFixedVectorsStatement` in
[FixedVectorsStatement](FixedVectorsStatement.md).
Worker 0 authored the proof terms and the initial explanation. Worker 59
verified the Library imports and original source context, retained those
proof terms, and expanded this explanation for submission.
The two evaluation formulas are definitional. Extensionality on the two
linear maps reduces the factorization formula to the same evaluation.
For naturality, evaluating either side at a fixed smooth functional `ell`
and a fixed vector `v` gives `ell (f v)`, again by definitional equality.

The four component lemmas remain in this proof module:

| Lemma | Implemented proof |
| --- | --- |
| `smoothDualFixedEquiv_apply` | The open-subgroup equivalence forgets the smoothness witness while retaining the same functional. Its evaluation equals `smoothDualPairing`, by `rfl`. |
| `smoothDualFixedRestriction_apply` | Restriction composes the underlying functional with the fixed-submodule inclusion. Evaluation is therefore the original pairing on that vector, by `rfl`. |
| `smoothDualFixedRestriction_factor` | `ext ell v` reduces equality of the linear maps to evaluation on a functional and a fixed vector. The equivalence and inclusions preserve these values; `rfl` closes the goal. |
| `smoothDualFixedRestriction_natural` | `ext ell v` reduces both sides to `ell (f v)`; `rfl` closes the goal. |

In the naturality equation, `f : rho -> sigma` induces pullback
`contragredientMap f` from smooth functionals on `sigma` to those on `rho`.
The map `fixedVectorsMap f K` goes from fixed vectors of `rho` to those of
`sigma`; its linear dual reverses this direction. Openness is required for
the fixed-functional equivalence and factorization. Restriction and its
naturality apply to every subgroup.

The closing theorem uses `omit [IsTopologicalGroup G]`, introduces the
topological-group instance inside the target, and supplies all four lemmas.
No averaging, finite-dimensional duality, or prior project theorem
is used. Its only direct import is the adjacent proposition module, with
construction dependencies documented there.

This internal proof concerns the elementary maps underlying Casselman
Chapter II, revision June 16, 2019, Section 3, page 6, opening paragraphs
and Proposition II.3.1:
`casselman-2019-smooth-representations`, SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
It does not prove that proposition's isomorphism assertion.
The retained original is
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
The source defines the smooth contragredient and states compact-open
fixed-vector duality under its ambient hypotheses. These four elementary
identities use only the explicit maps, which justifies their broader scope;
they assert neither injectivity nor surjectivity of restriction.

The target `Langlands.SmoothDualFixedVectorsStatement` is published in
`Langlands.Representation.Smooth.Contragredient.FixedVectorsStatement` at
Library `843c574c920aa9926ab56adf662c74b3cd4ed0e1`. Its construction imports are
`Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions` and
`Langlands.Representation.Smooth.FixedVectors.Definitions`; their transitive
imports supply smoothness, smooth parts and the dual constructions. The
published target and all its project imports match the local source files.
The transitive project imports are `Langlands.Representation.Dual.Definitions`,
`Langlands.Representation.Smooth.Definitions`,
`Langlands.Representation.Smooth.SmoothPart.Definitions`,
`Langlands.Representation.Smooth.Contragredient.Definitions`, and
`Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`.
All sixteen Lean/Markdown files in this eight-module closure remain unchanged.
This proof requires none of the pending compact-duality or reflexivity proofs.

All four component laws and the closing theorem remain one proof contribution.
The coefficient ring, group and two representation carriers have independent
universes `uR uG uV uW`. Coefficients form an arbitrary commutative ring.
The topological-group hypothesis is inside the proposition. No original
smoothness, admissibility, compactness, finite dimension, characteristic-zero
or Noetherian assumption is added. No topology is imposed on the coefficients
or modules. The full declaration type, including its outer parameters, is
retained.

The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`,
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The proof contains no placeholders or project axioms. Incremental Lake
compilation and exact full-declaration inspection with allowed assumptions
are machine checks; independent semantic review and current-Library
publication remain separate requirements.
