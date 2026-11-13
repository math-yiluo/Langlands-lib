# The valuation-theoretic Krasner stabilizer step: statement

This module defines the single proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_eq_of_fixed_of_closeStatement`
in
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner.Statements`.
It records exactly the signature of source unit M397.001. The module
supplies no proof of that proposition.

## Mathematical meaning and full parameters

The target is a closed `def ... : Prop`. Its body universally quantifies:

```lean
{K : Type u} {L : Type w}
[Field K] [Field L] [Algebra K L]
{base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
{target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
[base.valuation.HasExtension target.valuation]
(huniq :
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
    base target)
(σ : Gal(L/K)) (a b : target.valuationSubring)
```

All four universes `u, v, w, x` are independent: `u, w` are the field
carrier universes and `v, x` are their chosen value-group universes.
The published uniqueness predicate has five universe parameters; its
comparison value group is specialized to universe `x`, as required by
the actual source action. The separate extension instance uses the
supplied `Algebra K L` and asserts compatibility of the chosen target
valuation with the chosen base valuation.

Here `Gal(L/K)` is Mathlib notation for `L ≃ₐ[K] L`. The source signature
and this target have no finite-dimensionality or `IsGalois` instance
binder. Although the source module's introductory prose mentions a
finite Galois extension, its theorem has the general telescope above.

For this explanation only, let `A` denote the published
`valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq σ`.
It is the actual ring automorphism of `target.valuationSubring` induced
by the supplied field automorphism `σ`. The two remaining universally
quantified hypotheses are exactly:

```lean
(hfix : A b = b)
(hclose :
  A a ≠ a →
    IsDiscreteValuationRing.addVal target.valuationSubring (A a - a) <
      IsDiscreteValuationRing.addVal target.valuationSubring (a - b))
```

The conclusion is `A a = a`. Every occurrence of `A` in the Lean file
is written as the published action itself. No new action is defined.
Both differences lie in the chosen valuation ring, and `addVal` is
Mathlib's normalized additive valuation on that ring with codomain
`ℕ∞`, where zero has value `⊤`. Thus `hclose` keeps the strict inequality
and its direction: a nonzero displacement of `a` would have smaller
additive valuation than `a - b`. It remains conditional on `A a ≠ a`
and concerns this single supplied automorphism.

## Exact source correspondence

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean`,
lines 45–62](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean#L45-L62).
The complete source file has SHA-256
`80a7e3430c526226a0f830de5afaab50dd6476169a847e9b5ff74ef7c2f1ee8c`.
Its readable retained path is
[/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean>).
The entire file, lines 1–116, was read and its hash verified.

| Pinned source location | Target correspondence |
| --- | --- |
| Lines 27–36: universes, namespaces and section variables | Preserve the four independent universes, prefix the namespace with `Langlands.NYLL`, and quantify every section variable inside the closed proposition. |
| Line 45: `RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_eq_of_fixed_of_close` | Preserve the theorem's name under `Langlands.NYLL`, adding `Statement` and using `def ... : Prop`. |
| Lines 46–49: uniqueness, automorphism and integral elements | Reuse the published predicate at universes `u, v, w, x, x` and retain `σ`, `a`, and `b` in source order. |
| Lines 50–52: `hfix` | Preserve equality of the actual action on `b` with `b`. |
| Lines 53–60: `hclose` | Preserve the implication from nonfixity of `a` and the exact strict comparison of `addVal` on `A a - a` and `a - b`. |
| Lines 61–62: conclusion | Preserve equality of the actual action on `a` with `a`. |
| Lines 63–111: proof | Omitted; this contribution publishes only the Prop target. |

## Reused declarations and import adaptation

The sole import is
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut`.
The proposition reuses its exact declaration
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension`.
That module's published import closure provides:

- `Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension`
  from `RealLowerGroups.UniqueExtension`;
- `Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF` and its
  `valuationSubring` abbreviation from
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`;
- Mathlib's `Valuation.HasExtension`, `Gal(L/K)` notation, the canonical
  ring and DVR instances on the valuation ring, and
  `IsDiscreteValuationRing.addVal` from
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.

This replaces the broad upstream `RamificationDepth` import at line 7.
The source proof uses `addVal_valuationSubringAutOfUniqueExtension`
(M323.001) at lines 83–84, but that theorem is not needed to form this
target. The successful focused Lean check inspects this single declaration
and reports `statement_returns_prop: true` with level parameters
`["u", "v", "w", "x"]` in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
No new instances or auxiliary statements are introduced.

## Attribution and modification record

Worker 329 extracted this statement and wrote its Markdown on
13 November 2026. The adaptations are the namespace prefix, the
`Statement` suffix and Prop-valued definition, moving the complete source
telescope into its body, spelling the inferred uniqueness comparison
universe explicitly, narrowing the import, and omitting the proof and
the unnecessary `noncomputable section`. The mathematical hypotheses
and conclusion are unchanged.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No relevant erratum was found in the workspace or current Library
errata directories; the project's separate notes errata directory was
absent when checked.

The original Apache-2.0 copyright and author header is retained in the
Lean file: copyright 2026 Naganori Yamaguchi, all rights reserved;
authors Naganori Yamaguchi (assisted by OpenAI Codex).
The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged.
The NOTICE contains no source-specific `ValuationKrasner.lean` entry.
