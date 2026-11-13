# NYLL M024.006: additivity of the relative coset action

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.relativeCosetAction_addStatement`
by the theorem `Langlands.NYLL.ClassFormation.relativeCosetAction_add`.
The theorem's type is exactly that proposition applied to its source
parameters, `relativeCosetAction_addStatement A K L hLK a b q`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Statements`
(see [Statements.md](../Statements.md)). That published Lean/Markdown pair
and its complete imported chain remain unchanged. In particular the proof
does not import or restate the M024.002 theorem `relativeCosetAction_mk`.

## Target and parameters

The theorem has, in this order, implicit `G : IntegralRepGroupType` (the published alias of `Type 0`),
the instances `[Group G]` and `[TopologicalSpace G]`, explicit
`A : Rep ℤ G`, `K L : ClosedSubgroup G` and
`hLK : L.toSubgroup ≤ K.toSubgroup`, then explicit
`a b : ambientFixedAddSubgroup A L` and
`q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)`, the
statement's telescope with the same binder kinds. The representation
carrier contributes the statement's single universe parameter. No premise
is added. Unfolding the proposition gives

```lean
relativeCosetAction A K L hLK (a + b) q =
  relativeCosetAction A K L hLK a q +
    relativeCosetAction A K L hLK b q
```

The sum `a + b` is taken in the additive subgroup of `L`-fixed coefficients
(published M023.001), and the right-hand sum in the representation module
`A.V`. The published M024.001 `relativeCosetAction A K L hLK a` evaluates a
coset by acting on `a` with any representative.

## Implemented proof

The complete proof body is

```lean
  unfold relativeCosetAction_addStatement
  refine Quotient.inductionOn' q ?_
  intro k
  change A.ρ k.1 (a + b).1 = A.ρ k.1 a.1 + A.ρ k.1 b.1
  exact map_add (A.ρ k.1) a.1 b.1
```

The `unfold` exposes the displayed equation. Quotient induction reduces to a
coset given by a representative `k : K.toSubgroup`. On such a class each
`relativeCosetAction` term reduces definitionally to the action of `k`
(the `Quotient.liftOn'` computation that M024.002 records), so the
`change` states the goal as `A.ρ k.1 (a + b).1 = A.ρ k.1 a.1 + A.ρ k.1 b.1`.
Since the coercion of `a + b` is definitionally `a.1 + b.1`, additivity of
the linear map `A.ρ k.1` (`map_add`) closes it.

The original proof (lines 96–99) performs the same quotient induction and
the same `map_add` step, but reaches the representative form with
`simp only [relativeCosetAction_mk]`. Here that step is an explicit
definitional `change`, so the proof needs neither the unpublished M024.002
proof nor a local copy of it.

## Pinned source and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`, whose
whole-file SHA-256
`5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`
Worker 165 recomputed from the retained copy under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`
on 13 November 2026 UTC; it matches the
[port partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m024),
which records no patch10 edit for M024.
The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum note exists under `notes/errata/` in the
Library at commit `9b849caba7c63ede041b7fec49c90ceaafb08568`.

The passage is
[lines 87–99](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean#L87-L99):
docstring at line 87, theorem name and telescope at 88–92, equation at
93–95 and proof at 96–99. The enclosing context is namespace
`ClassFormation` (line 22), `noncomputable section` (line 29) and the
section variables at line 34.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `relativeCosetAction_add` | Published `relativeCosetAction_addStatement` |
| Proof `relativeCosetAction_add` | This theorem, same adapted name |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its exact body `L.toSubgroup.subgroupOf K.toSubgroup`, as in the statement |
| `relativeCosetAction`, `ambientFixedAddSubgroup` | Existing published data (M024.001, M023.001) |

Modifications by Worker 165 on 13 November 2026 UTC: prefix the namespace
with `Langlands.NYLL`; replace the source imports with the sole Statements
import; give the theorem the published proposition applied to its
parameters as its type and unfold it first; write the quotient binder with
the published `Subgroup.subgroupOf` body; replace
`simp only [relativeCosetAction_mk]` by the definitional `change` above;
omit the source `noncomputable section`, `open CyclicCohomology` and all
other source declarations. The original docstring, quotient induction and
`map_add` step are retained.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 165's dated modification
record. Worker 165 extracted this proof directly from the pinned original
and the published statement; no project draft was reused and there are no
project coauthors. The statement pair and its definitions (Worker 200)
are imported unchanged; no imported Library file is edited.

The unchanged inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained in
`repository_paths`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. A development `lean_check`
compiled the module with no errors or warnings, and declaration
inspection reported only the axioms `propext`, `Classical.choice` and
`Quot.sound`, with the single universe parameter of the statement.
Development compilation is separate from acceptance: publication under
`lean.proof@1` also requires the Lake, kernel and exact-target checks,
independent semantic review and Integrator publication.

This proof covers only M024.006. The other M024 units, the
`relativeNorm` definition M024.009 and every host class-formation, cup,
transfer, Tate or reciprocity target remain separate work.
