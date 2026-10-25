# Normalized integer valuation of a nonarchimedean local field

This module defines
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v` by extracting
only source unit M128.001 from Naganori Yamaguchi's NYLL ClassFieldTheory
library. The source is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`, lines 25–37](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L25-L37),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The original file's
SHA256 is `c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`.

The retained source registration is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The file is readable in that snapshot under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The associated attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the project's published errata lookup.

## Interface and construction

The complete interface is

```lean
noncomputable def v (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Additive Kˣ → Int
```

Here `u` is arbitrary. The field, valuative relation, topology and proof of
Mathlib's `IsNonarchimedeanLocalField K` are supplied by the caller. The
last class asserts that the topology comes from the valuative relation,
the space is locally compact, and that relation is nontrivial. There is no
restriction to a particular field or to universe zero, and no additional
choice of a host valuation or host order is an argument.

For `x : Additive Kˣ`, the definition performs these operations in order:

1. Recover the unit `Additive.toMul x : Kˣ` and coerce it to `K`.
2. Evaluate the actual `ValuativeRel.valuation K` on that element.
3. Apply Mathlib's order-preserving multiplicative isomorphism
   `_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` to obtain
   an element of `WithZero (Multiplicative Int)`.
4. Use `WithZero.unzero` to regard this value as a `Multiplicative Int`.
5. Apply `Multiplicative.toAdd` to return its integer exponent.

The nonzero certificate in step 4 is the original expression. The unit's
`ne_zero` proof and `Valuation.ne_zero_iff` show that its valuation is
nonzero; `map_ne_zero` transports that fact through the isomorphism. These
are existing Mathlib facts used directly to construct the value. No new
mathematical lemma or additional hypothesis supplies the certificate.
The definition is noncomputable because it uses Mathlib's chosen value-group
isomorphism.

The returned exponent is used without negation, preserving the source's
inverse-standard sign convention. This module supplies the function only.
A comparison with a separately supplied host `ord`, including its sign,
is a separate theorem obligation; no such comparison is claimed here.

## Exact source correspondence and scope

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v`, definition starting at line 29, source unit M128.001 | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v` |

The full parameter list, arbitrary universe, codomain, definition body and
nonzero certificate are unchanged. The `_root_` qualifier on
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` still refers to
Mathlib, rather than the adapted namespace. The only import is
`Mathlib.NumberTheory.LocalField.Basic`; no other NYLL module is required.
The extraction introduces no global instances or original-namespace aliases.

All other source declarations are outside this unit, including `v_apply`,
surjectivity, multiplication and inverse laws, and the uniformizer and
integer-unit results. The bundled `valuationUnitsMulHom` and `valuationMap`
definitions from M134 are also outside it. This definition does not establish
a valuation exact sequence, an Artin map, or a reciprocity theorem.

## Attribution and modifications

The source copyright and author header is retained verbatim: Copyright
(c) 2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all
rights reserved; authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. Unmodified copies of the original
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and [NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this extraction.
The upstream NOTICE lists no source-specific third-party entry for this
`NonarchimedeanLocalField/Basic.lean`; its other notices remain preserved
in the complete copy.

Worker 384 extracted M128.001, added the `Langlands.NYLL` namespace prefix,
removed the rest of the source file, and wrote this documentation on
25 October 2026. A prominent notice in the Lean header records the changes.
This extraction is made directly from the pinned original; no private
adaptation or wholesale NYLL dependency closure is incorporated.
