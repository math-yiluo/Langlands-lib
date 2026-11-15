# NYLL M020.008: `G_L` is closed in `G_K`

This module proves the published Library proposition
`Langlands.NYLL.KummerTheory.extensionSubgroup_isClosedStatement` by the
theorem `Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed`. The
theorem's type is exactly that proposition applied to its source parameters,
`extensionSubgroup_isClosedStatement K L hLK`.

Its target import is
`Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Statements`
([`Statements.lean`](../Statements.lean)). That published Lean/Markdown pair
and everything it imports are unchanged.

## Target and parameters

The theorem has one universe parameter, `u_2`, as the published proposition
does. Its parameters are, in this order:

1. implicit `{G : Type u_2}` with instances `[Group G] [TopologicalSpace G]`,
   bound by the theorem itself as in the source (the section variable line
   `{G : Type*} [Group G] [TopologicalSpace G]` is kept, as in the source, but
   is shadowed and so not part of the telescope; its `Type*` takes the name
   `u_1`);
2. explicit `(K L : ClosedSubgroup G)`;
3. explicit `hLK : L.toSubgroup ≤ K.toSubgroup`.

Unfolding the proposition gives

```lean
IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup)
```

where `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002) is the
abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`. So: if `L ≤ K` are
closed subgroups of a group `G` with a topology, then `L`, regarded as a
subgroup of `K`, is a closed subset of `K` with its subspace topology. No
topological group law is assumed or used.

## Implemented proof

The proof is the source tactic proof, unchanged.

1. `change IsClosed ((fun x : K.toSubgroup => (x : G)) ⁻¹' (L : Set G))`
   replaces the goal by the closedness of the preimage of `L` under the
   inclusion `K → G`. This is definitionally the proposition: unfolding the
   Statement definition, the abbreviation `extensionSubgroup` and Mathlib's
   `Subgroup.subgroupOf` (the comap of `L` along `K.subtype`), membership of
   `x` in the carrier is membership of `(x : G)` in `L`.
2. `exact L.isClosed'.preimage continuous_subtype_val` closes it: `L` is
   closed in `G` (the field `isClosed'` of Mathlib's `ClosedSubgroup`), and
   the preimage of a closed set under the continuous map `Subtype.val` is
   closed.

The development check of this module (diagnostic
`15bdf350-a85c-40df-9f3f-bfdad6d752dd`) reports no errors or warnings. The
theorem has the universe parameter `u_2`, and its axioms are only `propext`,
`Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.KummerTheory.extensionSubgroup_isClosedStatement`
  (M020.008 statement), used only by definitional unfolding.
- The published abbreviation `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
  (M004.002), reached through the import chain and opened in the file; it is
  used only by definitional unfolding.
- Mathlib's `ClosedSubgroup` and its field `isClosed'`
  (`Mathlib/Topology/Algebra/Group/ClosedSubgroup.lean`),
  `Subgroup.subgroupOf`, `IsClosed.preimage`
  (`Mathlib/Topology/Continuous.lean`, line 188) and `continuous_subtype_val`
  (`Mathlib/Topology/Constructions.lean`, line 380). Line numbers refer to
  Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

No other NYLL declaration is used, and no host class-formation, cup,
transfer, Tate or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean:135–142`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean#L135-L142).
Lines 135–136 are the docstring, 137–140 the signature and 141–142 the
proof. The theorem lies in `namespace KummerTheory` (line 25, with
`open CyclicCohomology` at line 27), the `noncomputable section` (line 31)
and `section ClosedCyclicSubextensions` (line 131) with the variable line 133
`{G : Type*} [Group G] [TopologicalSpace G]`. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m020)
lists this theorem as M020.008 (source unit from line 137; the next unit
starts at line 149). The whole-file SHA-256 is
`abedaf33dffa23e93392885b9c29e77ead8a9452ee32d9100614f6f0ac731033`,
recomputed by Worker 395 on 15 November 2026 UTC from the retained snapshot.

| Original in `KummerTheory` | Adapted in `Langlands.NYLL.KummerTheory` |
| --- | --- |
| Asserted type of `extensionSubgroup_isClosed` (M020.008) | Published `extensionSubgroup_isClosedStatement` in KummerAbelianCyclicFactors.Statements |
| Proof `extensionSubgroup_isClosed` | This theorem of the same adapted name in KummerAbelianCyclicFactors.U008.Proofs |

Worker 395 made only these changes on 15 November 2026 UTC:

- prefix the namespace with `Langlands.NYLL`;
- replace the two source imports by the sole published Statements import;
- state the theorem's type as the published proposition applied to
  `K L hLK`;
- open `Langlands.NYLL.CyclicCohomology` (the port of the source's
  `open CyclicCohomology`) so that `extensionSubgroup` resolves to the
  published abbreviation;
- omit the other declarations of the source file, including the later
  `variable [IsTopologicalGroup G]` line, which follows this theorem.

The section name, the variable line, the `noncomputable section`, the
docstring, the theorem name, the binders with their names and order, and the
two proof tactics are unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors. Worker 4918's statement is used unchanged.

The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M020.008. It is not a class-formation, cup, transfer,
Tate or reciprocity result.
