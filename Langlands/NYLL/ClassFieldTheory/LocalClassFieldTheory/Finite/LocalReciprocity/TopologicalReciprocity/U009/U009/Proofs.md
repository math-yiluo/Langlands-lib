# NYLL M257.009: closure of the commutator subgroup of a discrete group

This module proves the published Library proposition
`Langlands.NYLL.PortInternal.M257.d009Statement` by the theorem
`Langlands.NYLL.PortInternal.M257.d009`. The theorem's type is exactly that
proposition applied to its source parameters, `d009Statement G`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U009.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, an explicit `G : Type` and the instances
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]`.
There is no finiteness, local-field or Galois hypothesis.

Unfolding the published proposition gives

```lean
Subgroup.topologicalClosure (commutator G) = commutator G
```

where `commutator G` is Mathlib's commutator subgroup `⁅⊤, ⊤⁆` and
`Subgroup.topologicalClosure` is the subgroup whose carrier is the topological
closure of the carrier. The statement says that the commutator subgroup of a
discrete topological group is closed, i.e. equals its closure.

## Implemented proof

The complete proof body is

```lean
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_discrete _)
  · exact Subgroup.le_topologicalClosure _
```

`le_antisymm` splits the equality of subgroups into two inclusions, and works
directly on the stated type `d009Statement G`. For the inclusion of the
closure in the commutator subgroup, Mathlib's
`Subgroup.topologicalClosure_minimal` says that `s.topologicalClosure ≤ t`
whenever `s ≤ t` and `t` has closed carrier; it is applied with
`s = t = commutator G`, the inclusion `le_rfl`, and closedness of the carrier
from `isClosed_discrete`, since every set is closed in a discrete space. The
reverse inclusion is `Subgroup.le_topologicalClosure`.

Apart from stating the type as the published proposition, this is the
original proof verbatim. No auxiliary declaration, extra hypothesis, instance
or `simp` registration is introduced. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition `Langlands.NYLL.PortInternal.M257.d009Statement`
  in TopologicalReciprocity.U009.Statements.
- Mathlib's `le_antisymm`, `le_rfl`, `Subgroup.topologicalClosure_minimal`
  and `Subgroup.le_topologicalClosure`
  (`Mathlib/Topology/Algebra/Group/Subgroup.lean`) and `isClosed_discrete`
  (`Mathlib/Topology/Order.lean`), all available through the Statements
  module's import of `Mathlib.Topology.Algebra.Group.TopologicalAbelianization`.

No other proof and no local-field, host class-formation or reciprocity
theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:353–359`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean#L353-L359).
Lines 353–356 are the signature of the private theorem
`commutator_topologicalClosure_eq` in namespace `LocalClassFieldTheory`, and
357–359 the proof. The theorem has no docstring; the docstring of the Lean
theorem here is new. The enclosing section `TopologicalReciprocity` declares
local-field variables `K L` at lines 349–351, which do not occur in this theorem
and are omitted. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m257)
places this proof at M257.009 (source unit lines 353–362) after
M257.008.END, under the stable port-internal name
`Langlands.NYLL.PortInternal.M257.d009` because the source declaration is
private. The whole-file SHA-256 is
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted |
| --- | --- |
| Asserted type of private `commutator_topologicalClosure_eq` (M257.009) | Published `Langlands.NYLL.PortInternal.M257.d009Statement` in TopologicalReciprocity.U009.Statements |
| Proof of private `commutator_topologicalClosure_eq` | This public theorem `Langlands.NYLL.PortInternal.M257.d009` in TopologicalReciprocity.U009.U009.Proofs |

The adaptation renames the private theorem as above, replaces the original
imports by the sole published Statements import, omits the unrelated section
variables, namespace openings, `noncomputable section` and local instances,
and states the theorem's type as the published proposition applied to `G`.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 96's dated modification
record. Worker 96 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M257.009. The finite-level abelianization comparison
M257.010, topological local reciprocity and any host class-formation, cup,
transfer, Tate or reciprocity target are separate work.
