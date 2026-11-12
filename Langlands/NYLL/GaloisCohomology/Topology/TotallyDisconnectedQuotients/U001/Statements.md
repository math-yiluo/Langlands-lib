# Totally disconnected quotient groups: the M013.001 target

This module defines the closed proposition
`Langlands.NYLL.QuotientGroup.totallyDisconnectedSpace_of_isClosedStatement.{u} : Prop`.
It says that the quotient of a compact Hausdorff totally disconnected
topological group by a closed normal subgroup, with the quotient
topology, is totally disconnected. It is the statement phase of source
unit M013.001 in the
[NYLL partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m013).
Defining the proposition does not prove it.

## Complete closed telescope

Inside `Langlands.NYLL.QuotientGroup`, the definition is

```lean
def totallyDisconnectedSpace_of_isClosedStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)),
    TotallyDisconnectedSpace (G ⧸ N)
```

The definition has no parameters of its own and one arbitrary universe
`u`, declared by `universe u`; it is not restricted to `Type 0`. All
ten binders of the source theorem are quantified inside the
proposition, in the source order and with the source binder kinds:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `G : Type u` | implicit | The group carrier |
| `[Group G]` | instance-implicit | Group structure |
| `[TopologicalSpace G]` | instance-implicit | Topology on `G` |
| `[IsTopologicalGroup G]` | instance-implicit | Multiplication and inversion are continuous |
| `[CompactSpace G]` | instance-implicit | `G` is compact |
| `[T2Space G]` | instance-implicit | `G` is Hausdorff |
| `[TotallyDisconnectedSpace G]` | instance-implicit | `G` is totally disconnected |
| `N : Subgroup G` | explicit | The subgroup divided out |
| `[N.Normal]` | instance-implicit | Normality of `N` |
| `hN : IsClosed (N : Set G)` | explicit | The underlying set of `N` is closed in `G` |

The normality assumption stays an instance binder inside the
proposition; the module installs no instance. The source writes
`{G : Type*}`, whose anonymous universe is named `u` here.

## Meaning of the conclusion

`G ⧸ N` is Mathlib's quotient by a subgroup,
`QuotientGroup.instHasQuotientSubgroup`, the type
`Quotient (QuotientGroup.leftRel N)` of left cosets
(`Mathlib/GroupTheory/Coset/Defs.lean`, lines 90–95). Since `N` is
normal, it is the quotient group. Its topology is
`QuotientGroup.instTopologicalSpace N`
(`Mathlib/Topology/Algebra/Group/Quotient.lean`, lines 31–33), which is
`instTopologicalSpaceQuotient`, the topology coinduced by the class map
from `G` (`Mathlib/Topology/Constructions.lean`, lines 58–60). A
private development check printed the elaborated definition with
explicit arguments; its conclusion uses exactly these two instances.

`TotallyDisconnectedSpace X`
(`Mathlib/Topology/Connected/TotallyDisconnected.lean`, lines 34–49)
says that every preconnected subset of `X` has at most one point. The
proposition asserts only this property of `G ⧸ N`. It asserts no
compactness, separation or topological-group property of the quotient.

The quotient type and its topology depend on neither `[N.Normal]` nor
`hN`. Both are hypotheses of the proposition. The unused-variables
linter would therefore warn about the name `hN`. The Lean file keeps
the source name and turns that linter off for this one declaration with
`set_option linter.unusedVariables false in`.

The source keeps `[T2Space G]` and so does this target. Mathlib's
docstring of `ProfiniteGrp.of`
(`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean`,
lines 74–77) notes that a totally disconnected topological group is
already Hausdorff. A private development check found `T2Space G` by
`inferInstance` from the group, topology, topological-group and
total-disconnectedness instances alone. So retaining the premise does
not narrow the proposition. The hypotheses on `G` are those of a
profinite group.

## Original passage and adaptation

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Topology/TotallyDisconnectedQuotients.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Topology/TotallyDisconnectedQuotients.lean#L21-L97).
The complete 187-line file was read; its SHA-256 is
`cab3604efecf0e48f740c668abf5d2e22aa1436172cf5f6bb8c1e6c72ed72c63`.
The theorem lies in `namespace QuotientGroup` (lines 19–99). Its
docstring is at lines 21–22, the name at 23, the binders at 24–26, the
conclusion and `:= by` at 27, and the tactic proof at 28–97. The
task contract gives lines 21–95, which stop two lines before the end of
the proof (the last step `infer_instance` is at line 97). The whole
theorem was read through line 97. Its asserted type is

```lean
theorem totallyDisconnectedSpace_of_isClosed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N)
```

| Original | Adaptation |
| --- | --- |
| Asserted type of `QuotientGroup.totallyDisconnectedSpace_of_isClosed`, lines 23–27 | Closed `Langlands.NYLL.QuotientGroup.totallyDisconnectedSpace_of_isClosedStatement.{u}`, defined here |
| Theorem docstring, lines 21–22 | Retained verbatim on the definition |
| `{G : Type*}` | `{G : Type u}` with `universe u` |
| Tactic proof, lines 28–97 | Deferred to the exact theorem `Langlands.NYLL.QuotientGroup.totallyDisconnectedSpace_of_isClosed`, of type `totallyDisconnectedSpace_of_isClosedStatement.{u}` |
| Imports `Mathlib.Topology.Algebra.ClopenNhdofOne` and `Mathlib.Topology.Algebra.Group.Quotient`, lines 7–8 | Both retained unchanged |
| Module docstring, lines 10–15 | Replaced by a docstring for the statement only |
| M013.002–M013.004, lines 101–187 | Omitted; separate source units |

The namespace gains the `Langlands.NYLL` prefix. The ten source
binders move, in order and with their binder kinds, inside a closed
proposition. The only other addition is the local linter option above.
No instance, `simp` attribute or other declaration is added. Both
source imports are kept, so no import is added or removed; the
clopen-neighbourhood import also supplies
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` for the
deferred proof. The inventory records no patch10 change to this module. Worker 5176 extracted the statement directly from the
pinned original; no shared draft, compatibility patch or other
worker's unpublished work was reused.

The original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No `notes/errata/<source id>.md` exists for either source ID in the
workspace, the project or Library `e449cde988d4e97ab280b8d4d11262887ccc26e0`.

## Reuse search

In the approved Mathlib, no declaration concludes
`TotallyDisconnectedSpace` or `TotallySeparatedSpace` for a quotient
`G ⧸ N`. The file `Mathlib/Topology/Algebra/ClopenNhdofOne.lean`
supplies the tools
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`
(lines 44–54) and `ProfiniteGrp.closedSubgroup_eq_sInf_open`
(lines 56–86), not this statement. The quotient-topology file gives
`CompactSpace (G ⧸ N)` from `CompactSpace G` (lines 35–37) but no
disconnectedness.

Library `e449cde988d4e97ab280b8d4d11262887ccc26e0` has no general
statement of this kind. The related
`Langlands.openQuotientHom_profinite_of_finite_kernel`
(`Langlands/Topology/OpenSubgroupPowerQuotient.lean`, lines 124–148)
needs an open quotient homomorphism with finite kernel, while `N` here
is an arbitrary closed normal subgroup. The power-quotient results in
`Langlands/Global/Arithmetic/SUnitIdelePowerQuotient.lean` take
profiniteness of their quotients as hypotheses. TaskHub task search and
the staged candidates show no other work on this target.

## Deferred truth proof

This file contains no proof. The exact theorem
`Langlands.NYLL.QuotientGroup.totallyDisconnectedSpace_of_isClosed`,
of type `totallyDisconnectedSpace_of_isClosedStatement.{u}`, needs a
separate proof task after this target is accepted and published.

The source proof separates two distinct classes `x N` and `y N`. Put
`g = x⁻¹ * y`, so `g ∉ N`. The set `W = {u | g * u⁻¹ ∉ N}` is open,
because `N` is closed, and contains `1`. Mathlib's
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` gives an
open normal subgroup `V ⊆ W`. Then `K = N ⊔ V` is an open subgroup with
`g ∉ K`. Its image in `G ⧸ N` is open, as the class map is open, and
hence clopen. Its translate by the class of `x` is a clopen set that
contains `x N` but not `y N`. By
`totallySeparatedSpace_iff_exists_isClopen` the quotient is totally
separated, hence totally disconnected. Normality is used to form the
quotient homomorphism `QuotientGroup.mk' N` and the group structure on
`G ⧸ N`.

Every Mathlib name the source proof uses is present in the approved
Mathlib. A private development check, which is not part of this
candidate, ran the unchanged source tactic proof after
`intro G _ _ _ _ _ _ N _ hN` against this exact target without errors;
its axioms were `propext`, `Classical.choice` and `Quot.sound`. That
check is only evidence of feasibility, not a published proof.

## Development validation

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`)
compiled this module with no errors or warnings. Inspection of the
declaration reports kind `definition`, the single universe parameter
`u` and `statement_returns_prop: true`. Upstream used Lean 4.35.0-rc2
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Compilation is
neither independent acceptance nor publication.

## Attribution and remaining obligations

The original 2026 Naganori Yamaguchi copyright, license and author
header, including “Naganori Yamaguchi (assisted by OpenAI Codex)”, is
retained verbatim, followed by a dated modification record. The
existing Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained
unchanged. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The normality instance for the identity component (M013.002), the
total disconnectedness of the quotient by the identity component
(M013.003) and `ContinuousMonoidHom.connectedComponentOfOne_le_ker`
(M013.004) remain separate units. This support statement discharges
no host class-formation, cup-product, transfer or Tate-cohomology
target.
