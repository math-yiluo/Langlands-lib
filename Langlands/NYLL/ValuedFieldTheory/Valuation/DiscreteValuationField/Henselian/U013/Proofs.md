# The valuation ring of a Henselian DVF is a DVR (NYLL M104.013)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.HenselianDVF.valuationSubring_isDiscreteValuationRingStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.HenselianDVF.valuationSubring_isDiscreteValuationRing`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem keeps the statement's binders in their order: implicit
`K : Type u` with `[Field K]` (the section variables) and explicit
`F : HenselianDVF.{u, v} K`. Its type is
`valuationSubring_isDiscreteValuationRingStatement F`, which unfolds to
`IsDiscreteValuationRing F.valuationSubring`. Here `F.valuationSubring` is the
published abbreviation for `F.toDVF.valuationSubring`, the valuation subring
`F.valuation.valuationSubring` of the chosen valuation
`F.valuation : Valuation K F.ValueGroup`, which carries the structure field
instance `F.valuation.IsRankOneDiscrete`.

Mathematically: the valuation ring of a field with a rank-one discrete
valuation is a discrete valuation ring (Serre, *Local Fields*, Chapter I,
Section 1, Proposition 1, as cited by Mathlib). The Henselian hypothesis of
`F` plays no role.

## Implemented proof

The proof is the term
`Valuation.valuationSubring_isDiscreteValuationRing F.valuation`, Mathlib's
instance stating that the valuation subring of a valuation `v` on a field is a
DVR when the value group of `v` is cyclic and nontrivial. Both side
conditions are found by instance search from the structure field
`F.valuation.IsRankOneDiscrete`, through Mathlib's `IsRankOneDiscrete`
instances (`Mathlib.RingTheory.Valuation.Discrete.Basic`). The resulting type
`IsDiscreteValuationRing F.valuation.valuationSubring` agrees with the target
by unfolding the statement and the abbreviations `HenselianDVF.valuationSubring`
and `DVF.valuationSubring`, which the elaborator does.

The source proof is `F.toDVF.valuationSubring_isDiscreteValuationRing`, the
theorem M103.011 for the underlying DVF. That theorem was not yet in the
Library when this proof was written; its source body
(`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`, line 92)
is exactly `Valuation.valuationSubring_isDiscreteValuationRing F.valuation`,
which is used here directly for `F.toDVF.valuation` (written `F.valuation`).
No declaration named after M103.011 is added.

The proof uses only Mathlib and the published NYLL definitions `HenselianDVF`,
`DVF` and their `valuationSubring` abbreviations. No auxiliary declaration,
instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi, [`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean:251–253`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean#L251-L253)
(partition unit lines 251–255; docstring at line 250; section variables at
line 199 inside `namespace HenselianDVF`, line 197).

| Original (namespace `ValuationTheory.DiscreteValuationField.HenselianDVF`) | Adapted |
| --- | --- |
| Theorem `valuationSubring_isDiscreteValuationRing`, lines 251–253 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `IsDiscreteValuationRing F.valuationSubring` (line 252) | `valuationSubring_isDiscreteValuationRingStatement F` |
| Term `F.toDVF.valuationSubring_isDiscreteValuationRing` (line 253) | Its source body `Valuation.valuationSubring_isDiscreteValuationRing F.valuation` (Basic.lean line 92) |

Adaptations: the namespace gains the `Langlands.NYLL` prefix; the source imports
are replaced by the single statement import; the conclusion is written as the
published statement applied to `F`; the citation of M103.011 is replaced by
its one-term source proof; the `noncomputable section` is omitted.

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
The whole source file `Henselian.lean` has SHA-256
`cce4a6ecfed6076732a5041ad23935a638de6eb5c3c35287d289c8b1717e0cf2`, recomputed by
Worker 740 on 16 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m104)
lists this unit in module M104 (no patch10 edit applies). The source file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`, whose
line 92 is quoted above, is module M103 of the same pinned snapshot.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
