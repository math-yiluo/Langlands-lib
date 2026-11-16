# NYLL M024.010: coercing a relative norm gives the coset-sum norm value

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.relativeNorm_apply_coeStatement`
by the theorem `Langlands.NYLL.ClassFormation.relativeNorm_apply_coe`.
The theorem's type is exactly that proposition applied to its source
parameters, `relativeNorm_apply_coeStatement A K L hLK a`, with the finite
coset-type instance supplied by elaboration.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Statements`
(see [Statements.md](../Statements.md)). That published Lean/Markdown pair and
its complete imported chain remain unchanged.

## Target and parameters

The theorem has, in this order, implicit `G : IntegralRepGroupType` (the
published alias of `Type 0`), the instances `[Group G]` and
`[TopologicalSpace G]`, explicit `A : Rep ℤ G`, `K L : ClosedSubgroup G` and
`hLK : L.toSubgroup ≤ K.toSubgroup`, the instance
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`, then
explicit `a : ambientFixedAddSubgroup A L`: the statement's telescope with the
same binder kinds. The representation carrier contributes the single universe
parameter. No premise is added: only the relative coset type is assumed
finite, with no normality, topological-group or continuity assumption.
Unfolding the proposition gives

```lean
((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
  relativeNormValue A K L hLK a
```

that is, the underlying element of `A.V` of the relative norm of `a` (the
published M024.009 homomorphism `relativeNorm`) is the published M024.005
coset-sum norm value `relativeNormValue A K L hLK a`, the sum over all left
cosets of `L.toSubgroup.subgroupOf K.toSubgroup` in `K.toSubgroup` of the
coset actions on `a`.

## Implemented proof

The complete proof is the term `rfl`, as in the source. The published
`relativeNorm` is the additive homomorphism whose `toFun` sends `a` to the
subtype element `⟨relativeNormValue A K L hLK a, relativeNormValue_fixed A K L hLK a⟩`
of `ambientFixedAddSubgroup A K`. Applying the bundled homomorphism and
taking the subtype value reduce definitionally to the first component
`relativeNormValue A K L hLK a`, so both sides are definitionally equal. The
named proposition `relativeNorm_apply_coeStatement` is itself a definition
whose body is this equation, so `rfl` also checks against the named target
without a separate unfolding step. No theorem is used.

## Pinned source and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`, whose
whole-file SHA-256
`5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`
Worker 744 recomputed from the retained copy under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`
on 16 November 2026 UTC. The
[port partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m024)
records no patch10 edit for M024. The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; the
attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The passage is
[lines 163–172](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean#L163-L172):
docstring at line 163, `@[simp]` at 164, theorem name and telescope at
165–169, equation at 170–171 and proof `rfl` at 172. The enclosing context is
namespace `ClassFormation` (line 22), `noncomputable section` (line 29) and
the section variables at line 34.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `relativeNorm_apply_coe` | Published `relativeNorm_apply_coeStatement` |
| Proof `relativeNorm_apply_coe` | This theorem, same adapted name, same proof `rfl` |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its exact body `L.toSubgroup.subgroupOf K.toSubgroup`, as in the statement |
| `relativeNorm`, `relativeNormValue` | Existing published data (M024.009, M024.005) |
| `ambientFixedAddSubgroup` | Existing published data (M023.001) |

Modifications by Worker 744 on 16 November 2026 UTC: prefix the namespace
with `Langlands.NYLL`; replace the source imports with the sole Statements
import; give the theorem the published proposition applied to its parameters
as its type; write `extensionSubgroup K L hLK` as the published
`Subgroup.subgroupOf` body; omit the `@[simp]` attribute (the theorem's
stated type is the named proposition rather than a displayed equation, so
the source simp-lemma registration is not reproduced),
the source `noncomputable section`, `open CyclicCohomology`,
`open scoped BigOperators` and all other source declarations. The original
docstring and proof term are retained.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 744's dated modification
record. Worker 744 extracted this proof directly from the pinned original and
the published statement; no project draft was reused and there are no
project coauthors. The statement pair (Worker 96) is imported unchanged; no
imported Library file is edited.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained in
`repository_paths`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A development
`lean_check` compiled the module with no errors or warnings, and declaration
inspection reported only the axioms `propext`, `Classical.choice` and
`Quot.sound`, with one universe parameter. Development compilation is
separate from acceptance: publication under `lean.proof@1` also requires the
Lake, kernel and exact-target checks, independent semantic review and
Integrator publication.

This proof covers only M024.010. The task context records that the later
M071.024 proof (Task 5866) depends on it; the M073.005 proof of this task
does not import it. Every host
class-formation, cup, transfer, Tate or reciprocity target remains separate
work.
