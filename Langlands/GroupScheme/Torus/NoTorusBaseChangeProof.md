# Absence of tori under arbitrary field extension

`Langlands.GroupScheme.noTorusBaseChange.{u}` proves exactly
`Langlands.GroupScheme.NoTorusBaseChangeStatement.{u}` from
`Langlands.GroupScheme.Torus.NoTorusBaseChangeStatement`.
The theorem has no arguments outside the proposition and retains its
single arbitrary universe parameter `u`.

For arbitrary fields `k K : Type u` with `Algebra k K`, a smooth affine group scheme receiving only trivial homomorphisms from ground-field tori also receives only trivial homomorphisms from tori after base change to `K`. The ambient group need not be connected.

## Implemented proof

Apply `noTorusBaseChangeReduction` to `noTorusUnipotent`. The reduction passes through the unipotent identity component, its base change and the triviality of homomorphisms from tori into unipotent groups.

Every reduction and input theorem appearing in the proof term is listed below.
Names and modules have the prefix `Langlands.GroupScheme`.

| Theorem | Module |
| --- | --- |
| `noTorusBaseChangeReduction` | `Torus.NoTorusBaseChangeReduction` |
| `noTorusUnipotent` | `Torus.NoTorusUnipotent` |

All applications use the proposition's universe `u`. The Lean proof is the
composition above; no structural premise remains as an extra hypothesis.

## Provenance

This is a derived proof assembled from the existing Library theorems named above,
following the route recorded in the note
`notes/group-schemes/composable-targets-2026-11-08.md`. It adds a direct proof of
the existing proposition. It introduces no new statement or independent
translation of literature.
