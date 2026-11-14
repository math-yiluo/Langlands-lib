# NYLL M022.001: membership in the extension subgroup

This module proves the published Library proposition
`Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iffStatement` by the
theorem `Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iff`. The
theorem's type is exactly that proposition applied to its source parameters,
`mem_extensionSubgroup_iffStatement K L hLK k`.

Its sole direct import is
`Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, an implicit group `G : Type*` (one universe
parameter) with instances `[Group G] [TopologicalSpace G]`, and the explicit
parameters `K L : ClosedSubgroup G`, the containment
`hLK : L.toSubgroup ≤ K.toSubgroup` and an element `k : K.toSubgroup`. As in
the source and the statement, `hLK` does not occur in the conclusion.

Unfolding the published proposition gives

```lean
k ∈ L.toSubgroup.subgroupOf K.toSubgroup ↔ (k : G) ∈ L
```

that is, `k ∈ G_K` lies in `G_L` regarded as a subgroup of `G_K` exactly
when its image in `G` lies in `G_L`.

## Implemented proof

The proof term is `Iff.rfl`. By Mathlib's definition, `H.subgroupOf K` is the
preimage `H.comap K.subtype`, so membership of `k` in it unfolds to
`K.subtype k ∈ H`, that is `(k : G) ∈ L.toSubgroup`. Membership in the closed
subgroup `L` is, through its `SetLike` instance, membership in its underlying
subgroup `L.toSubgroup`. Both sides are therefore the same proposition up to
definitional unfolding, and the statement definition unfolds to this
equivalence, so the kernel accepts `Iff.rfl`.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring, the theorem's own
`{G : Type*}` binder and the `@[simp]` attribute of source line 32. No
auxiliary declaration, extra hypothesis or instance is introduced. The
development check reports no errors or warnings and only the axioms
`propext` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iffStatement` in
  KummerAbelianAssembly.U001.Statements.
- Mathlib's `Subgroup.subgroupOf` and `ClosedSubgroup`
  (`Mathlib/Topology/Algebra/Group/ClosedSubgroup.lean`), used only through
  definitional unfolding.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean:30–38`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean#L30-L38).
Lines 30–31 are the docstring, 32 the `@[simp]` attribute, 33–37 the
signature and 38 the proof `Iff.rfl`. The source conclusion is
`k ∈ extensionSubgroup (G := G) K L hLK ↔ (k : G) ∈ L`, where NYLL's
`CyclicCohomology.extensionSubgroup K L hLK` is the abbreviation
`L.toSubgroup.subgroupOf K.toSubgroup`; the published statement writes this
body directly. The section variable line 28
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` is shadowed by
the theorem's own binder. The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m022)
places this proof at M022.001 (source unit lines 33–42). The whole-file
SHA-256 is
`ca4ad38a7ed46fa029400e2c7718faf0587b4206731c82c8c45d6839b719f54c`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `KummerTheory` | Adapted in `Langlands.NYLL.KummerTheory` |
| --- | --- |
| Asserted type of `mem_extensionSubgroup_iff` (M022.001) | Published `mem_extensionSubgroup_iffStatement` in KummerAbelianAssembly.U001.Statements |
| Proof `mem_extensionSubgroup_iff` | This theorem of the same adapted name in KummerAbelianAssembly.U001.U001.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, omits the unused
`open CyclicCohomology` and the shadowed section variable line, keeps the
`noncomputable section`, the docstring and `@[simp]`, and states the
theorem's type as the published proposition applied to `K L hLK k`. The
proof is unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M022.001. The quotient-action evaluation M022.002,
the later KummerAbelianAssembly units and any host class-formation, cup,
transfer, Tate or reciprocity target are separate work.
