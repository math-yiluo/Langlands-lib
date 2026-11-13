# NYLL M024.002: relative coset action on a representative

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.relativeCosetAction_mkStatement`
by the theorem `Langlands.NYLL.ClassFormation.relativeCosetAction_mk`.
The theorem's type is exactly that proposition applied to its source
parameters, `relativeCosetAction_mkStatement A K L hLK a k`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Statements`
(see [Statements.md](../Statements.md)). That published Lean/Markdown pair
and its complete imported chain remain unchanged.

## Target and parameters

The theorem has, in this order, implicit `G : IntegralRepGroupType`
(the published alias of `Type 0`), the instances `[Group G]` and
`[TopologicalSpace G]`, explicit `A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup`, `a : ambientFixedAddSubgroup A L`
and `k : K.toSubgroup`. These are the statement's parameters in the same
order and binder kinds; the representation carrier contributes the
statement's single universe parameter. No premise is added. Unfolding the
proposition gives

```lean
relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1
```

Here `relativeCosetAction A K L hLK a` is the published M024.001 function on
the relative coset type `K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup`,
defined by `Quotient.liftOn'` of `fun k => A.ρ k.1 a.1` (well defined
because `a` is fixed by every element of `L`). The assertion says that its
value at the coset of a representative `k` is the action of `k` on `a`.

## Implemented proof

The complete proof term is `rfl`. The proposition unfolds by
definition to the displayed equation, and the quotient lift
`Quotient.liftOn'` evaluated at the class `QuotientGroup.mk k` reduces
definitionally to `A.ρ k.1 a.1`. This is the original proof, unchanged.

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
[lines 58–65](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean#L58-L65):
docstring at line 58, `@[simp]` at 59, theorem name and telescope at
60–63, equation at 64 and proof `rfl` at 65. The enclosing context is
namespace `ClassFormation` (line 22), `noncomputable section` (line 29) and
the section variables at line 34.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `relativeCosetAction_mk` | Published `relativeCosetAction_mkStatement` |
| Proof `relativeCosetAction_mk` | This theorem, same adapted name, proof `rfl` |
| `relativeCosetAction`, `ambientFixedAddSubgroup` | Existing published data (M024.001, M023.001) |

Modifications by Worker 165 on 13 November 2026 UTC: prefix the namespace
with `Langlands.NYLL`; replace the source imports with the sole Statements
import; give the theorem the published proposition applied to its
parameters as its type; omit the source `noncomputable section`,
`open CyclicCohomology` and all other source declarations. The original
docstring and proof are retained.

The source `@[simp]` attribute is not retained. The theorem's type is an
application of the non-reducible `relativeCosetAction_mkStatement`, which
`simp` does not unfold when registering a lemma, so the attribute would not
provide the original rewriting behavior: in a private development experiment
(not part of this contribution), with the attribute registered locally on
this theorem, `simp only [relativeCosetAction_mk]` made no progress on the
representative equation. Later proofs can use
`relativeCosetAction_mk A K L hLK a k` as an equation by type ascription,
or the same definitional reduction directly, as the M024.006 and M024.008
proofs in this group do.

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

This proof covers only M024.002. The other M024 units, the
`relativeNorm` definition M024.009 and every host class-formation, cup,
transfer, Tate or reciprocity target remain separate work.
