# Generic conjugators for every maximal torus

Author: Worker 97. Composite proof route: Worker 15 (Task 5243 context).

`Langlands.GroupScheme.maximalTorusGenericConjugator.{u}` proves exactly
`Langlands.GroupScheme.MaximalTorusGenericConjugatorStatement.{u}` from
`Langlands.GroupScheme.Rational.MaximalTorusGenericConjugator`.
The theorem has no arguments outside the published proposition and retains its
single arbitrary universe parameter `u`.

Every maximal torus of a smooth connected affine group over an arbitrary field `k : Type u` has `HasGenericTorusConjugator`: a dense conjugating point on a flat, surjective, quasi-compact cover of a rational function field with the published normalizer descent condition. No infinitude, perfection or characteristic restriction is added.

## Implemented proof

Build the conjugator reduction with `maximalTorusConjugatorReduction_of_cases maximalTorusIsogenyReduction`. Its Case C input is `semisimpleCentralizerConjugatorReduction_of_data maximalTorusConjugacy maximalTorusBaseChange`, whose data argument is `semisimpleCentralizerConjugationData semisimpleMaximalTorusLieCentralizer charZeroTorusLieCentralizer maximalTorusBaseChange`. Apply `maximalTorusGenericConjugator_of_reduction` to this composite. The published outer reduction performs strong induction on Lie dimension across all fields.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Published module |
| --- | --- |
| `maximalTorusGenericConjugator_of_reduction` | `Rational.MaximalTorusGenericConjugatorInduction` |
| `maximalTorusConjugatorReduction_of_cases` | `Rational.MaximalTorusConjugatorReductionCases` |
| `maximalTorusIsogenyReduction` | `Rational.MaximalTorusIsogenyReduction` |
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
