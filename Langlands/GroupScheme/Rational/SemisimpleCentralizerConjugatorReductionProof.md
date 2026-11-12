# The semisimple centralizer conjugator reduction

Author: Worker 97. Composite proof route: Worker 15 (Task 5243 context).

`Langlands.GroupScheme.semisimpleCentralizerConjugatorReduction.{u}` proves exactly
`Langlands.GroupScheme.SemisimpleCentralizerConjugatorReductionStatement.{u}` from
`Langlands.GroupScheme.Rational.MaximalTorusConjugatorReductionCases`.
The theorem has no arguments outside the published proposition and retains its
single arbitrary universe parameter `u`.

For arbitrary fields `k : Type u`, the maximal tori of smooth connected affine groups satisfying `HasNoncentralGeometricSemisimpleElement` have `HasSmallerTorusConjugatorReduction` below the ambient Lie dimension. All transfer and normalizer conditions are those of the published proposition.

## Implemented proof

First obtain generic data by `semisimpleCentralizerConjugationData semisimpleMaximalTorusLieCentralizer charZeroTorusLieCentralizer maximalTorusBaseChange`. Apply `semisimpleCentralizerConjugatorReduction_of_data` to `maximalTorusConjugacy`, `maximalTorusBaseChange` and these data. This turns the generic conjugating point into the required transfer to a smaller group.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Published module |
| --- | --- |
| `semisimpleCentralizerConjugatorReduction_of_data` | `Rational.MaximalTorusConjugatorCaseC` |
| `maximalTorusConjugacy` | `Absolute.MaximalTorusConjugacyProof` |
| `maximalTorusBaseChange` | `Torus.MaximalBaseChangeProof` |
| `semisimpleCentralizerConjugationData` | `Rational.MaximalTorusConjugatorCaseCData` |
| `semisimpleMaximalTorusLieCentralizer` | `Lie.TorusLieCentralizerProof` |
| `charZeroTorusLieCentralizer` | `Lie.CharZeroTorusLieCentralizerProof` |

All applications use the published universe `u`. The Lean proof is the
composition above; no structural premise remains as an extra hypothesis.
The earlier composite terms are repeated in this module, so this candidate
depends only on published modules.

## Provenance

This is a derived proof assembled from the existing Library theorems named above,
following the route recorded by Worker 15 in the context of Task 5243
(`054c9e79-c59d-4325-a96b-8c82a40df80b`, revision 1) and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`. It adds a direct proof of
the existing proposition. It introduces no new statement or independent
translation of literature. The original statement and its imports are unchanged.
