# NYLL M023.002: membership in the ambient fixed additive subgroup

This module proves the published Library proposition
`Langlands.NYLL.KummerTheory.mem_ambientFixedAddSubgroup_iffStatement` by the
theorem `Langlands.NYLL.KummerTheory.mem_ambientFixedAddSubgroup_iff`. The
theorem's type is exactly that proposition applied to its source parameters,
`mem_ambientFixedAddSubgroup_iffStatement A H a`.

Its sole direct import is
`Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U002.Statements`
([`Statements.lean`](Statements.lean)). That published Lean/Markdown pair and
everything it imports are unchanged.

## Target and parameters

The theorem has, in this order, the section variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (source line 30,
kept verbatim), then the explicit parameters `A : Rep ℤ G`,
`H : ClosedSubgroup G` and `a : A.V`. `IntegralRepGroupType` is the published
alias `Langlands.NYLL.IntegralRepGroupType := Type 0`. As for the statement,
Lean generalizes the universe of the representation space, so the theorem has
the single universe parameter `u_1`.

Unfolding the published proposition gives

```lean
a ∈ ambientFixedAddSubgroup A H ↔ ∀ h : H.toSubgroup, A.ρ h.1 a = a
```

Here `ambientFixedAddSubgroup A H` is the published M023.001 definition: the
additive subgroup of `A.V` of elements fixed by every element of the closed
subgroup `H`. The theorem says that `a` lies in this subgroup exactly when
`A.ρ h a = a` for every `h ∈ H`.

## Implemented proof

The proof term is `Iff.rfl`, unchanged from the source. The kernel checks it
by definitional unfolding:

1. The statement definition unfolds to the displayed equivalence.
2. `ambientFixedAddSubgroup A H` is an `AddSubgroup A.V` structure whose
   carrier is `{a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}`. Its definition is
   written `by exact { carrier := … }`, which elaborates to that structure
   term.
3. Membership `a ∈ S` in an `AddSubgroup` is, through Mathlib's `SetLike`
   instance, membership of `a` in the carrier set. For the set-builder
   carrier this is the predicate `∀ h : H.toSubgroup, A.ρ h.1 a = a`.

Both sides are therefore the same proposition up to definitional unfolding,
and `Iff.rfl` closes the goal.

The `@[simp]` attribute of source line 48 is omitted. The stated type is the
proposition constant `mem_ambientFixedAddSubgroup_iffStatement A H a` rather
than an equivalence, so the attribute would not register the source rewrite
rule. The same choice was made in the published M008.019 proof and in this
task's M009.007 proof. The development check of this module reports no errors
or warnings. The theorem has the universe parameter `u_1`, and its axioms are
only `propext` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.KummerTheory.mem_ambientFixedAddSubgroup_iffStatement` in
  KummerDelta.U002.Statements.
- The published M023.001 definition
  `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`
  (KummerDelta.U001.Definitions) and the alias `IntegralRepGroupType`,
  reached through the import chain.
- Mathlib's `Rep`, `ClosedSubgroup`, `AddSubgroup` and its `SetLike`
  membership, used only through definitional unfolding.

No other NYLL theorem and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean:46–53`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean#L46-L53).
Lines 46–47 are the docstring, 48 the `@[simp]` attribute, 49–52 the
signature and 53 the proof `Iff.rfl`. The theorem lies in
`namespace KummerTheory` (lines 22–178), after `open CyclicCohomology`
(line 24), in the `noncomputable section` (lines 28–177) with the file's only
`variable` command at line 30. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m023)
lists this theorem as M023.002 (source unit from line 49; the next unit
starts at line 57). The partition's patch P1 for this module concerns only
the later units M023.003–M023.007 and does not touch these lines. The
whole-file SHA-256 is
`6778a3be3b28518c10a0288dd21befed505cf6bed556590eab1f4dba82f166b8`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `KummerTheory` | Adapted in `Langlands.NYLL.KummerTheory` |
| --- | --- |
| Asserted type of `mem_ambientFixedAddSubgroup_iff` (M023.002) | Published `mem_ambientFixedAddSubgroup_iffStatement` in KummerDelta.U002.Statements |
| Proof `mem_ambientFixedAddSubgroup_iff` | This theorem of the same adapted name in KummerDelta.U002.Proofs |

Worker 395 made these changes on 14 November 2026 UTC:

- prefix the namespace with `Langlands.NYLL`;
- replace the source imports (lines 7–9) by the sole published Statements
  import;
- state the theorem's type as the published proposition applied to
  `A H a`;
- omit the `@[simp]` attribute, as explained above, the unused
  `open CyclicCohomology` and all other source declarations.

The `noncomputable section`, the `variable` line, the docstring, the theorem
name, the binders and their order, and the proof `Iff.rfl` are unchanged.
They needed no change for the approved environment.

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
are no project coauthors. Worker 5454's statement and Worker 232's M023.001
definition are used unchanged.

The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with SHA-256
values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires the Lake
build, kernel and exact-target checks, unchanged statement and dependency
checks, independent semantic review and Integrator publication.

This proof covers only M023.002. The Delta subgroup M023.003 and the later
KummerDelta units, and any Kummer-theory, class-formation, cup, transfer,
Tate or reciprocity target, are separate work.
