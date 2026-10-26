# General norm image subgroup

`Langlands.NYLL.LocalFieldTheory.localNormSubgroup` defines the subgroup of
base-field units obtained as norms of extension-field units. Its complete
declaration telescope is

```lean
(K L : Type u) [Field K] [Field L] [Algebra K L] : Subgroup Kˣ
```

Here `u` is arbitrary and shared by the two fields. The body is exactly
`(Langlands.NYLL.LocalFieldTheory.normUnits K L).range`, using the published
norm homomorphism. That homomorphism is `Units.map (Algebra.norm K)`.
Mathlib's `MonoidHom.range` supplies the subgroup structure; its carrier
consists of units `x : Kˣ` for which there exists `y : Lˣ` with
`normUnits K L y = x`.

There is no finite-dimensional, separable, Galois, local-field, valuation,
or topology hypothesis. The term uses Mathlib's general algebra norm,
including its convention for algebras that are not finite modules.

## Original and adapted declaration

This extraction is M093.001 of the accepted NYLL declaration partition.
Its original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Lines 1–5 contain the attribution, line 24 declares the source universes,
and lines 26–28 contain this definition. The original file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete original file was read.

The retained original is in the `n-yamaguchi-0729--ClassFieldTheory/source/`
directory of registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The related attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The published partition records no patch10 modification to this module.
The project and current Library errata locations contain no applicable
erratum for either registered source.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.localNormSubgroup` | `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |

The namespace prefix changes; the source parameters, result type and body
are preserved. The unused universe `v` is omitted. Although the imported
`normUnits` supports independent universes, this definition retains the
source's single shared universe.

## Imports and dependency pruning

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`.
The current Library's corresponding Lean and Markdown were checked before
reuse. Mathlib's range construction was checked in
`Mathlib/Algebra/Group/Subgroup/Ker.lean`, where `MonoidHom.range` and
`MonoidHom.mem_range` define the subgroup and its membership condition.
The published normUnits import supplies the necessary Mathlib declarations
transitively.

The partition's M092.END prerequisite conservatively means completion of
the whole original NormUnits module. This particular definition uses only
the already published M092.002 definition. It needs none of M092's
evaluation, negation or tower results. The source module's additional
direct imports of Finset, quotient groups, finite dimensionality and norm
basics are therefore omitted here. This pruning concerns the direct
imports and required NYLL declarations; those Mathlib modules may still
occur transitively.

A Lean-service build and declaration inspection succeeded with Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, without errors or
warnings. Inspection reports a definition with the single universe parameter
`u`. A separate private check printed its full unapplied type, assigned the
unapplied constant to exactly the telescope above, and verified the range
body by reflexivity. That check also succeeded without errors or warnings.
Together these checks verify the reduced import closure and the preserved
declaration; they do not constitute independent semantic acceptance.

## Host comparison and scope

The existing `Langlands.LocalClassField.normSubgroup` in
`Langlands/ClassFieldTheory/Local/Norms.lean` requires
`[FiniteDimensional K L]`. Under that specialization, in a shared universe
and with aligned field and algebra instances, its body and the definition
here both describe `(Units.map (Algebra.norm K)).range`.
The host `Langlands.LocalClassField.localNormSubgroup` further specializes
to actual p-adic field carriers and supplies finite dimensionality from
their common p-adic base. With those instances aligned, it describes the
same actual range on those carriers. The host definitions are unchanged;
no comparison theorem is part of this unit.

This file contains just the subgroup definition. Norm quotients, their
group instances, quotient maps, evaluation statements and proofs belong
to later units. It makes no assertion about an Artin map, a norm kernel,
reciprocity, openness or finite index.

## Attribution and changes

The original copyright and author header is retained verbatim, including
Naganori Yamaguchi's 2026 copyright and the author credit
“Naganori Yamaguchi (assisted by OpenAI Codex)”. The source is Apache-2.0.
Its unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain included through
the submission's `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE does not list `NormQuotient.lean`.

Worker 583 extracted and documented M093.001 on 26 October 2026, added
the namespace prefix, replaced the source imports with the published
normUnits module, and omitted the unused universe and all other source
declarations. The source telescope and body were retained. No other
worker's draft or patch10 implementation was reused.
