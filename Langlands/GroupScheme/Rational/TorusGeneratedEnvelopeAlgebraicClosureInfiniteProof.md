# The closed torus envelope over an algebraic closure

Author: Worker 97. Composite proof route: Worker 15 (Task 5243 context).

`Langlands.GroupScheme.torusGeneratedEnvelopeAlgebraicClosureInfinite.{u}` proves exactly
`Langlands.GroupScheme.TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement.{u}` from
`Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureStatement`.
The theorem has no arguments outside the published proposition and retains its
single arbitrary universe parameter `u`.

For every infinite field `k : Type u` and every smooth connected affine group scheme over `k`, the fixed closed torus envelope commutes with base change to the algebraic closure. The equality is of subgroup functors on every test scheme, including nonreduced schemes.

## Implemented proof

Apply `torusGeneratedEnvelopeAlgebraicClosureInfinite_of` to `maximalTorusBaseChange`, `maximalTorusConjugacy` and `rationalMaximalTorusConjugateDensity`. The reduction combines stability of maximal tori, geometric conjugacy and density over an infinite field to obtain the exact envelope equality.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Published module |
| --- | --- |
| `torusGeneratedEnvelopeAlgebraicClosureInfinite_of` | `Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction` |
| `maximalTorusBaseChange` | `Torus.MaximalBaseChangeProof` |
| `maximalTorusConjugacy` | `Absolute.MaximalTorusConjugacyProof` |
| `rationalMaximalTorusConjugateDensity` | `Rational.RationalMaximalTorusDensityProof` |

All applications use the published universe `u`. The Lean proof is the
composition above; no structural premise remains as an extra hypothesis.

## Provenance

This is a derived proof assembled from the existing Library theorems named above,
following the route recorded by Worker 15 in the context of Task 5243
(`054c9e79-c59d-4325-a96b-8c82a40df80b`, revision 1) and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`. It adds a direct proof of
the existing proposition. It introduces no new statement or independent
translation of literature. The original statement and its imports are unchanged.
