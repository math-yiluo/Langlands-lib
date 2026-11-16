# The maximal ideal of a Henselian DVF is nonzero (NYLL M104.015)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.HenselianDVF.maximalIdeal_ne_botStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.HenselianDVF.maximalIdeal_ne_bot`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem keeps the statement's binders in their order: implicit
`K : Type u` with `[Field K]` (the section variables) and explicit
`F : HenselianDVF.{u, v} K`. Its type is `maximalIdeal_ne_botStatement F`,
which unfolds to `F.maximalIdeal ≠ ⊥`. Here `F.maximalIdeal` is the published
abbreviation for `F.toDVF.maximalIdeal`, that is
`IsLocalRing.maximalIdeal F.valuationSubring` for the valuation subring of the
chosen rank-one discrete valuation `F.valuation`.

Mathematically: the maximal ideal of the valuation ring of a discretely
valued field is not the zero ideal. The Henselian hypothesis of `F` plays no
role.

## Implemented proof

The proof first records the instance
`IsDiscreteValuationRing F.valuationSubring`, given by Mathlib's
`Valuation.valuationSubring_isDiscreteValuationRing F.valuation` (the value
group of `F.valuation` is cyclic and nontrivial by instance search from the
structure field `F.valuation.IsRankOneDiscrete`; this is the same term as the
proof of M104.013). It then applies Mathlib's
`IsDiscreteValuationRing.not_a_field F.valuationSubring :
IsLocalRing.maximalIdeal F.valuationSubring ≠ ⊥`, the field of the class
`IsDiscreteValuationRing` saying that a DVR is not a field. The local-ring
instance inside that statement comes from the DVR instance, while the target
uses `ValuationSubring.isLocalRing`; both are proofs of the proposition
`IsLocalRing F.valuationSubring`, so the two maximal ideals agree
definitionally by proof irrelevance and the term has the target type.

The source proof is `F.toDVF.maximalIdeal_ne_bot`, the theorem M103.030 for
the underlying DVF, which the source proves from a uniformizer `π` of the
valuation (`DVF.exists_uniformizer`, `DVF.uniformizer_mem_maximalIdeal`): a
nonzero element of the maximal ideal. That theorem was not yet in the Library
when this proof was written, so this proof takes the shorter Mathlib route
above instead: it neither cites nor reproves M103.030, M103.020 or M103.021,
and adds no declaration under their names.

The proof uses only Mathlib (`Mathlib.RingTheory.Valuation.Discrete.Basic`
and `Mathlib.RingTheory.DiscreteValuationRing.Basic`, available through the
statement module's imports) and the published NYLL definitions `HenselianDVF`,
`DVF` and their `valuationSubring` and `maximalIdeal` abbreviations. The
`haveI` is local to the proof term; no auxiliary declaration, global instance
or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi, [`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean:262–264`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean#L262-L264)
(partition unit lines 262–266; docstring at line 261; section variables at
line 199 inside `namespace HenselianDVF`, line 197).

| Original (namespace `ValuationTheory.DiscreteValuationField.HenselianDVF`) | Adapted |
| --- | --- |
| Theorem `maximalIdeal_ne_bot`, lines 262–264 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `F.maximalIdeal ≠ ⊥` (line 263) | `maximalIdeal_ne_botStatement F` |
| Term `F.toDVF.maximalIdeal_ne_bot` (line 264) | `IsDiscreteValuationRing.not_a_field` for the Mathlib DVR instance of M104.013 |

Adaptations: the namespace gains the `Langlands.NYLL` prefix; the source imports
are replaced by the single statement import; the conclusion is written as the
published statement applied to `F`; the citation of M103.030 is replaced by
the Mathlib route described above; the `noncomputable section` is omitted.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 740's dated modification record. Worker 740
extracted this proof directly from the pinned original and the published
statement module; there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`cce4a6ecfed6076732a5041ad23935a638de6eb5c3c35287d289c8b1717e0cf2`, recomputed by
Worker 740 on 16 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m104)
lists this unit in module M104 (no patch10 edit applies). The source proof of
M103.030 mentioned above is in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`, lines
304–314, module M103 of the same pinned snapshot.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
