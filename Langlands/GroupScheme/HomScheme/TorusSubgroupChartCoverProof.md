# Chart covers of closed torus subgroups over every base

Author: Worker 97. Composite proof route: Worker 15 (Task 5243 context).

`Langlands.GroupScheme.TorusSubgroupModuli.chartCover.{u}` proves exactly
`Langlands.GroupScheme.TorusSubgroupModuli.ChartCoverStatement.{u}` from
`Langlands.GroupScheme.HomScheme.TorusSubgroupChartStatements`.
The theorem has no arguments outside the published proposition and retains its
single arbitrary universe parameter `u`.

For every base scheme `S : Scheme.{u}` and every smooth affine group scheme over `S`, there is a family of open charts of the actual closed torus subgroup functor covering all field points. The base is arbitrary and no finite type hypothesis is added.

## Implemented proof

Apply `TorusSubgroupModuli.chartCoverReduction` to `TorusSubgroupModuli.finiteTypeChartCover`. The published reduction extends chart covers from affine bases of finite type over the integers to arbitrary bases.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Published module |
| --- | --- |
| `TorusSubgroupModuli.chartCoverReduction` | `HomScheme.TorusSubgroupChartCoverReductionProof` |
| `TorusSubgroupModuli.finiteTypeChartCover` | `HomScheme.SmoothTorusSubgroupRepresentabilityProof` |

All applications use the published universe `u`. The Lean proof is the
composition above; no structural premise remains as an extra hypothesis.

## Provenance

This is a derived proof assembled from the existing Library theorems named above,
following the route recorded by Worker 15 in the context of Task 5243
(`054c9e79-c59d-4325-a96b-8c82a40df80b`, revision 1) and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`. It adds a direct proof of
the existing proposition. It introduces no new statement or independent
translation of literature. The original statement and its imports are unchanged.
