# Cardinal indices of subgroup inclusions

This is the namespaced adaptation of M006.010 and M006.011 from Naganori
Yamaguchi's NYLL project, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`.
The source was read in full. Its SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.

| Source unit and location | Original name | Adapted declaration |
| --- | --- | --- |
| M006.010, lines 131–137 (definition at 136) | `ClassFormation.intersectionIndexCardinal` | `Langlands.NYLL.ClassFormation.intersectionIndexCardinal` |
| M006.011, lines 139–141 (definition at 140) | `ClassFormation.relativeIndexCardinal` | `Langlands.NYLL.ClassFormation.relativeIndexCardinal` |

For a group `G : Type u` and arbitrary subgroups `L K`, the first definition is
`Cardinal.mk (K ⧸ L.subgroupOf K) : Cardinal.{u}`. Here `L.subgroupOf K`
is the subgroup of `K` whose elements also belong to `L`. Thus the coset type
measures the index of their intersection in `K`. There is no normality,
inclusion or finiteness premise on this definition.

For implicit subgroups `L K` and an explicit proof `hLK : L ≤ K`, the second
definition returns that same cardinal. It retains the inclusion proof in its
domain, as in the source, although the defining value does not use that proof.
Both declarations are noncomputable data with exactly the source universe `u`
and group parameter. They preserve infinite cardinalities.

The source's `universe u v` and section variables at lines 23–25 also introduce
`{D : Type v} [Group D]`. Neither definition refers to `D`, so Lean omits it
and `v` from their elaborated constants. The extraction writes only the retained
variables `{G : Type u} [Group G]`. A private whole-constant comparison with
definitions reconstructed in the complete original section checks this omission
and the parameter visibility and order by definitional equality.

The only mathematical dependencies are Mathlib's `Subgroup.subgroupOf`,
the coset quotient `QuotientGroup.quotient` and `Cardinal.mk`. The focused imports
`Mathlib.Algebra.Group.Subgroup.Map`, `Mathlib.GroupTheory.Coset.Defs` and
`Mathlib.SetTheory.Cardinal.Basic` suffice.
The source imports `Nyll.GaloisCohomology.GroupTheory.QuotientTower`; that module,
the earlier M006 kernel-coset constructions and their theorems are not needed by
these two definitions. The focused Lean build verifies this smaller import set.

Mathlib's `Subgroup.relIndex` in `Mathlib.GroupTheory.Index` is a natural number:
it is the `Nat.card` of this same coset type, and assigns zero to infinite
indices. It cannot replace the cardinal-valued data with the stated scope.
The Library was searched for the two source names and cardinal-index data;
no existing exact definition was found. Existing Mathlib coset and cardinal
constructions are reused directly in the bodies.

The changes are namespace prefixing, extraction to a focused module, replacement
of the source import, omission of unused section variables and file-level
documentation. The two definition bodies, declaration kinds, noncomputable
status and docstrings are unchanged. No instance is introduced. This contribution
provides these two data definitions only; the finite-boundary, tower and
image–kernel theorems remain separate statement and proof obligations.

The original copyright, license and author header is retained in the Lean file.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`).
No applicable errata note was found. The upstream Apache-2.0 files remain at
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
