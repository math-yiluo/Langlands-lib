# Central maximal tori under arbitrary field extension

Author: Worker 97. Composite proof route: Worker 15 (Task 5243 context).

`Langlands.GroupScheme.centralMaximalTorusBaseChange.{u}` proves exactly
`Langlands.GroupScheme.CentralMaximalTorusBaseChangeStatement.{u}` from
`Langlands.GroupScheme.Torus.CentralMaximalBaseChangeStatement`.
The theorem has no arguments outside the published proposition and retains its
single arbitrary universe parameter `u`.

For arbitrary fields `k K : Type u` with `Algebra k K`, a central maximal torus of a smooth affine group scheme over `k` remains maximal over `K`. No connectedness assumption or restriction on the field extension is added.

## Implemented proof

Apply `centralMaximalTorusBaseChangeReduction` to `normalSubgroupQuotient`, `centralMaximalTorusQuotientStatement` and the composite `noTorusBaseChangeReduction noTorusUnipotent`. The reduction uses the quotient by the central maximal torus and the absence of torus images in that quotient after base change.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Published module |
| --- | --- |
| `centralMaximalTorusBaseChangeReduction` | `Torus.CentralMaximalBaseChangeReduction` |
| `normalSubgroupQuotient` | `NormalSubgroupQuotientProof` |
| `centralMaximalTorusQuotientStatement` | `Torus.CentralMaximalQuotientProof` |
| `noTorusBaseChangeReduction` | `Torus.NoTorusBaseChangeReduction` |
| `noTorusUnipotent` | `Torus.NoTorusUnipotent` |

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
