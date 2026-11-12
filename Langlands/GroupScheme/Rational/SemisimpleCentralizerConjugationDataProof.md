# Generic semisimple centralizer conjugation data

Author: Worker 97. Composite proof route: Worker 15 (Task 5243 context).

`Langlands.GroupScheme.semisimpleCentralizerConjugationDataUnconditional.{u}` proves exactly
`Langlands.GroupScheme.SemisimpleCentralizerConjugationDataStatement.{u}` from
`Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseC`.
The theorem has no arguments outside the published proposition and retains its
single arbitrary universe parameter `u`.

For every field `k : Type u`, every smooth connected affine group scheme and every maximal torus with the published noncentral geometric semisimple-element hypothesis, the generic conjugation data of `SemisimpleCentralizerConjugationDataStatement` exist. This includes the smaller Lie dimension, dense conjugating point and all-test-scheme conjugation condition.

## Implemented proof

Apply `semisimpleCentralizerConjugationData` to `semisimpleMaximalTorusLieCentralizer`, `charZeroTorusLieCentralizer` and `maximalTorusBaseChange`. The published reduction supplies both characteristic cases, so the theorem has no characteristic restriction.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Published module |
| --- | --- |
| `semisimpleCentralizerConjugationData` | `Rational.MaximalTorusConjugatorCaseCData` |
| `semisimpleMaximalTorusLieCentralizer` | `Lie.TorusLieCentralizerProof` |
| `charZeroTorusLieCentralizer` | `Lie.CharZeroTorusLieCentralizerProof` |
| `maximalTorusBaseChange` | `Torus.MaximalBaseChangeProof` |

All applications use the published universe `u`. The Lean proof is the
composition above; no structural premise remains as an extra hypothesis.

## Provenance

This is a derived proof assembled from the existing Library theorems named above,
following the route recorded by Worker 15 in the context of Task 5243
(`054c9e79-c59d-4325-a96b-8c82a40df80b`, revision 1) and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`. It adds a direct proof of
the existing proposition. It introduces no new statement or independent
translation of literature. The original statement and its imports are unchanged.
