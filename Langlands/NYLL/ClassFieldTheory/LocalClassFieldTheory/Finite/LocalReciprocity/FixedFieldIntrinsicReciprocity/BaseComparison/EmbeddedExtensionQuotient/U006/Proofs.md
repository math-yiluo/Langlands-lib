# Embedded extension quotients: the equivalence on transported classes

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement`
(source row M274.006) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is the published statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U006.Statements`.
That module imports the definition of
`ambientEmbeddedExtensionQuotientEquivGaloisGroup` (U005 Definitions, source
row M274.005). The published Lean/Markdown pair and everything it imports
stay unchanged.

## Target

The parameters are fields `K F E : Type` in a tower with `F / K` finite
separable and `E / F` finite Galois, and `j : E →ₐ[K] SeparableClosure K`.
The local data are:

- `i`, the restriction of `j` to `F`;
- the `F`-algebra structures on `SeparableClosure F`, through
  `separableClosure F (AlgebraicClosure F)`, and on `SeparableClosure K`,
  through `i`;
- an `F`-algebra isomorphism
  `e : SeparableClosure F ≃ₐ[F] SeparableClosure K`;
- `jI := e.symm.toAlgHom.comp jF`, where `jF` is `j` regarded as an
  `F`-algebra map;
- `EI := finiteGaloisAbstractExtensionOfEmbedding F E jI`;
- the closed subgroups `H₀` and `J₀` fixing `i(F)` and `j(E)`, with
  `hJH : J₀ ≤ H₀`.

For every `tau : (intrinsicAbstractBase F).toSubgroup` the target asserts

```lean
ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e
    (QuotientGroup.mk (intrinsicBaseEquivAmbientEmbeddedField K F i e tau)) =
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI
    (QuotientGroup.mk tau)
```

## Implemented proof

The proof first unfolds the statement's local data with `dsimp only`. It
then reintroduces the source's local data as tactic `let`s, in this order:

- `i` and the `F`-algebra structure on `SeparableClosure K`;
- `e` and `tau`;
- `jF`, `jI`, `EI`, `H₀`, `J₀` and `hJH`, with the source proof of `hJH`;
- the two normality instances `hSourceNormal := EI.normal` and
  `hTargetNormal := ambientEmbeddedExtensionSubgroup_normal K F E j e`;
- `psi := intrinsicBaseEquivAmbientEmbeddedField K F i e`.

The `dsimp only` step removes the statement's own `letI` instances. These
`let`s put the two normality instances back in the local context, where the
`QuotientGroup.congr` terms below find them as instances. In a test without
these two `let`s, the declaration exceeded the default heartbeat limit, and
also a limit of 1,000,000.

The definition of `ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e`
(U005) is the composite of `(QuotientGroup.congr _ _ psi hmap).symm` with
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI`. Here `hmap`
is the equality of `psi`'s image of the intrinsic extension subgroup with
the ambient one. The proof therefore restates the goal by `change` as

```lean
finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI
    ((QuotientGroup.congr
      (extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below)
      (extensionSubgroup H₀ J₀ hJH) psi _).symm
      (QuotientGroup.mk (psi tau))) =
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI
    (QuotientGroup.mk tau)
```

The last argument of `QuotientGroup.congr` is the subgroup equality. Its
placeholder `_` is solved by unifying with the goal, that is, by the proof
inside the U005 definition. `congr 1` reduces the goal to equality of the
two quotient classes. A second `change` rewrites the inverse of
`QuotientGroup.congr` on a class definitionally as
`QuotientGroup.mk (psi.symm (psi tau)) = QuotientGroup.mk tau`. The final
`rw [psi.symm_apply_apply]` closes it.

The proof uses only Mathlib and the declarations the statement module
imports. These are the U005 definition, `ambientEmbeddedExtensionSubgroup_normal`
(M274.003), `intrinsicBaseEquivAmbientEmbeddedField` (M273.006),
`finiteGaloisAbstractExtensionOfEmbedding` (M097.005) and
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` (M090.009).

## Relation to the original proof

The source proof (lines 536–596) has the same steps, with one difference.
Before the first `change`, the source proves a local `hmap` by citing the
M274.002 theorem `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField` and
passes it to `QuotientGroup.congr`. Since the argument is a proof, any proof
gives the same term up to definitional proof irrelevance. This proof
therefore leaves it as the placeholder `_` and omits `hmap` and the citation.
So it does not depend on a proof of M274.002.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>),
SHA-256 `6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The theorem `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk`
has its docstring at lines 484–485, its signature at lines 486–535 and its
proof at lines 536–596. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk` | Published `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement` (U006 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk` (this module) |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes:

- the namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`;
- the theorem proves the published closed proposition instead of restating
  its telescope;
- the local `hmap` and its M274.002 citation are replaced by a placeholder;
- the source imports are replaced by the single statement import;
- all other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M274.006 proof.
