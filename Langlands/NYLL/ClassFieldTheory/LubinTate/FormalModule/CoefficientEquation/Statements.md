# Fixed-uniformizer coefficient equation: reduction and scalar targets

This module states the signatures of the five theorems M337.001, M337.002,
M337.003, M337.004 and M337.006. It contains proposition definitions; it does
not prove them.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/CoefficientEquation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/CoefficientEquation.lean).
Its SHA-256 is
`87df634a8db769fcf0684ed48933bb957d27a2f8c21e1f50cd58565395933f65`.
It is readable in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The whole 89-line source file was read, together with the header of its
imported `Series.lean`. The project errata lookup contains no entry for this
source.

The original copyright, Apache-2.0 and author header is preserved in the Lean
file. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
Worker 485 made the adaptations listed below. No patch10 edit affects this
source module.

## Context and parameters

All five targets are in `Langlands.NYLL.LubinTate.SameUniformizer`, the source
namespace `LubinTate.SameUniformizer` (lines 25–26) prefixed by
`Langlands.NYLL`. Each target retains the source section variables of lines
23 and 30–31:

- independent universes `u v`;
- implicit `{K : Type u}` with `[Field K]`;
- implicit `{F : LocalField.{u, v} K}`, the published
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`
  (adapted M334.001), which the source opened at line 28;
- implicit `{π : F.valuationSubring}`.

Every target also keeps the explicit uniformizer hypothesis
`(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))` in first position,
as in the source. It is Mathlib's `Valuation.IsUniformizer`: the chosen
valuation of `π`, viewed in `K`, equals the generator of the value group of
the rank-one discrete valuation. The rank-one discrete instance comes from the
stored complete-discrete predicate of the published `CompleteDVF` parent.

The imported abbreviations are those of the published LocalField module:
`F.valuationSubring` is the type underlying the actual valuation subring of
the chosen valuation, and `F.residueMap` is the canonical
`IsLocalRing.residue` homomorphism to its residue field. Arithmetic
`1 - π ^ r` and `(1 - π ^ r) * x` takes place in that valuation subring.

## Exact targets

| Source unit and lines | Target, relative to the namespace above | Further parameters after `hπ` | Proposition |
| --- | --- | --- | --- |
| M337.001, lines 33–38; signature 34–36 | `residueMap_uniformizer_eq_zeroStatement` | none | `F.residueMap π = 0` |
| M337.002, lines 40–50; signature 41–44 | `uniformizer_dvd_of_residueMap_eq_zeroStatement` | `{a : F.valuationSubring} (ha : F.residueMap a = 0)` | `π ∣ a` |
| M337.003, lines 52–57; signature 53–56 | `residueMap_uniformizer_pow_eq_zeroStatement` | `{r : ℕ} (hr : r ≠ 0)` | `F.residueMap (π ^ r) = 0` |
| M337.004, lines 59–68; signature 60–63 | `isUnit_one_sub_uniformizer_powStatement` | `{r : ℕ} (hr : r ≠ 0)` | `IsUnit (1 - π ^ r)` |
| M337.006, lines 77–84; signature 79–82 | `existsUnique_one_sub_uniformizer_pow_mul_eqStatement` | `{r : ℕ} (hr : r ≠ 0) (b : F.valuationSubring)` | `∃! x : F.valuationSubring, (1 - π ^ r) * x = b` |

The divisibility in M337.002 is in the valuation subring, not in `K`.
The unit in M337.004 is a unit of the valuation subring. The positivity of
`r` is expressed, as in the source, by the hypothesis `r ≠ 0` on a natural
number. In Lean the hypothesis parameters are spelled `_hπ`, `_ha` and `_hr`
because a proposition's body does not use them; their binder kinds, order and
types are those of the source.

## Omitted source declaration M337.005

Source lines 70–75 state `existsUnique_mul_eq_of_isUnit`: for a commutative ring
`R` and `a : R` with `IsUnit a`, every `b` has a unique `x` with `a * x = b`.
By the task contract it is not ported as a NYLL target: its proof term
`(IsUnit.isUnit_iff_mulLeft_bijective.mp ha).existsUnique b` is the exact
Mathlib expression, and the later proof of M337.006 will use it directly.
No declaration of this module corresponds to M337.005.

## Adaptations

The following are all modifications to the selected source declarations and
their surrounding interface:

- Extract the five theorem signatures into this focused statement module;
  omit M337.005 (above) and every proof.
- Prefix the source namespace and its opened namespace
  `LocalFieldTheory.DiscreteValuationField` by `Langlands.NYLL`, and append
  `Statement` to each source theorem name.
- Replace each theorem and its proof with a `def` returning `Prop`; preserve
  each signature's universes, section variables, parameters, binder kinds and
  conclusion. Rename the unused hypotheses `hπ`, `ha` and `hr` to `_hπ`, `_ha`
  and `_hr`.
- Replace the source import `Nyll.ClassFieldTheory.LubinTate.FormalModule.Series`
  by `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`.
  The signatures use only the LocalField structure and its residue-data
  abbreviations, which Series reached through its own LocalField import; no
  Lubin–Tate series declaration occurs in them. Drop the source imports
  `Mathlib.Algebra.Group.Units.Basic` and `Mathlib.Logic.Function.Basic`, which
  serve the omitted proofs and M337.005. `IsUnit`, `∃!`, divisibility and
  `Valuation.IsUniformizer` are supplied through the published import chain
  (the latter by `Mathlib.RingTheory.Valuation.Discrete.Basic`).
- Remove the unused `noncomputable section` wrapper, and replace the module
  documentation and the theorem docstrings with statement-specific ones.

## Later proof routes

The source proofs use four CompleteDVF lemmas of M107 that are not in the
Library: `residue_eq_zero_iff` (.019), `residue_ne_zero_iff_isUnit` (.020),
`uniformizer_mem_maximalIdeal` (.023) and `maximalIdeal_eq_span_uniformizer`
(.024). The task contract names their checked Mathlib replacements:
`IsLocalRing.residue_eq_zero_iff`, `IsLocalRing.residue_ne_zero_iff_isUnit`,
`(Valuation.mem_maximalIdeal_iff (v := F.toCompleteDVF.valuation)).2 hπ.val_lt_one`
and `Valuation.IsUniformizer.is_generator (v := F.toCompleteDVF.valuation) hπ`.
M337.004 also uses `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits`, and
M337.006 uses `IsUnit.isUnit_iff_mulLeft_bijective` and
`Function.Bijective.existsUnique`. These descriptions identify the later proof
tasks; this module makes no proof claim. Each exact theorem, with the source
name in this namespace, is to be routed to a `lean.proof@1` task only after its
target has been published.

## Development verification

The module was compiled in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) against the published LocalField
module, with no warnings or errors. Separate exact-declaration inspections of
all five targets succeeded, reported `statement_returns_prop: true` and
universe parameters `u` and `v`. A private draft proved all five targets with
the replacements above in the same environment. Development compilation,
inspection and the draft do not establish independent semantic acceptance or
publish any proof.
