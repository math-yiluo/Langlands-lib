# Maximal tori remain maximal after field extension

`Langlands.GroupScheme.maximalTorusBaseChangeForward.{u}` proves exactly
`Langlands.GroupScheme.MaximalTorusBaseChangeForwardStatement.{u}` from
`Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction`.
The theorem has no arguments outside the published proposition and retains its
single arbitrary universe parameter `u`.

For arbitrary fields `k K : Type u` with `Algebra k K`, every maximal torus of a smooth affine group scheme over `k` remains maximal over `K`. This proves the published forward implication, with no connectedness or characteristic restriction.

## Implemented proof

Apply `maximalTorusBaseChangeForwardReduction` to `torusCentralizerSmooth` and the central composite `centralMaximalTorusBaseChangeReduction normalSubgroupQuotient centralMaximalTorusQuotientStatement (noTorusBaseChangeReduction noTorusUnipotent)`. The outer reduction works in the smooth torus centralizer, where the torus is central.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Published module |
| --- | --- |
| `maximalTorusBaseChangeForwardReduction` | `Torus.MaximalBaseChangeForwardReduction` |
| `torusCentralizerSmooth` | `Torus.CentralizerSmoothProof` |
| `centralMaximalTorusBaseChangeReduction` | `Torus.CentralMaximalBaseChangeReduction` |
| `normalSubgroupQuotient` | `NormalSubgroupQuotientProof` |
| `centralMaximalTorusQuotientStatement` | `Torus.CentralMaximalQuotientProof` |
| `noTorusBaseChangeReduction` | `Torus.NoTorusBaseChangeReduction` |
| `noTorusUnipotent` | `Torus.NoTorusUnipotent` |

All applications use the published universe `u`. The Lean proof is the
composition above; no structural premise remains as an extra hypothesis.
The earlier composite terms are repeated in this module, so the module
depends only on published modules.

## Provenance

This is a derived proof assembled from the existing Library theorems named above,
following the route recorded in the Library note
`notes/group-schemes/composable-targets-2026-11-08.md`. It adds a direct proof of
the existing proposition. It introduces no new statement or independent
translation of literature. The original statement and its imports are unchanged.
