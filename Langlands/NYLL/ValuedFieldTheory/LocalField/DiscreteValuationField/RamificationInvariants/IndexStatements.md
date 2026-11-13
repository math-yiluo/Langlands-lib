# Nonzero and positive ramification-index targets

This module adapts M343.002–003 from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean#L54-L70)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source file has SHA-256
`e8f6193618b69865b663a601b6063cbab7231d8ce39259501305d26ffc262e4d`.
The complete source file was read, including its namespace, universe and
variable context at lines 21–34. The selected declarations are exactly
lines 54–59 and 65–70; the preceding documentation occupies lines 49–53
and 61–64.

The source is available under the registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
in `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL source erratum was found in the current Library errata
notes. The port inventory records no patch10 modification to M343.

## Statements and complete parameter context

Both declarations are in
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension`.
They have the following common outer telescope, in source order:

```lean
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
[base.valuation.HasExtension target.valuation]
[Module.IsTorsionFree base.valuationSubring target.valuationSubring]
```

Here `CompleteDVF` is the published
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`.
All four universes `u v w x` remain independent. The field types are
implicit, the field and algebra structures are instance binders, the two
chosen complete-DVF packages are explicit, and the valuation-extension and
torsion-free hypotheses remain instance binders. In particular, the last
hypothesis is explicitly declared on each definition even though its body
does not use the proof. No finite-dimensionality, finite-module or scalar-tower
hypothesis is added.

For this telescope, the two bodies are exactly:

| Declaration | Body, with result type `Prop` |
| --- | --- |
| `ramificationIndex_ne_zeroStatement` | `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal ≠ 0` |
| `ramificationIndex_posStatement` | `0 < Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` |

These are proposition definitions. The module supplies no proof of either
proposition.

## Canonical objects and the inlined source wrapper

The source conclusions use
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
base.toDVF target.toDVF`.
Source M108.003, lines 53–56 of
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean#L53-L56),
defines that wrapper by
`Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal`, with explicit
ideal type annotations. That file has SHA-256
`e8999a99fc7ff6c38bd68742b9c7779decfbb2d042f60779bd2386d7950232b5`;
its header, imports, parameter context and definitions through line 130
were read.

The adapted targets inline this exact body at the canonical projections of
the supplied `CompleteDVF` packages. The published `CompleteDVF.toDVF` goes
through `toHenselianDVF.toDVF` and retains the chosen valuation and value
group. Its valuation-subring and maximal-ideal abbreviations reduce to
the same objects as those of the original complete package:

| Source expression | Adapted expression |
| --- | --- |
| `base.toDVF.valuationSubring` | `base.valuationSubring`, definitionally `base.valuation.valuationSubring` |
| `target.toDVF.valuationSubring` | `target.valuationSubring`, definitionally `target.valuation.valuationSubring` |
| `base.toDVF.maximalIdeal` | `base.maximalIdeal`, the canonical local-ring maximal ideal |
| `target.toDVF.maximalIdeal` | `target.maximalIdeal`, the canonical local-ring maximal ideal |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF` | `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` |

Mathlib's `Valuation.HasExtension.instAlgebra_valuationSubring` supplies the
canonical algebra on these actual valuation subrings. It is the algebra
used by the source wrapper and by `Module.IsTorsionFree` here.
`Ideal.ramificationIdx'` uses this algebra's map and is the supremum of
the natural numbers `n` for which the mapped base ideal is contained in the
`n`th power of the target ideal. The two source conclusions therefore
agree definitionally with the displayed bodies under the documented
wrapper substitution. No new ramification-index definition or chosen ideal
is introduced.

## Exact name correspondence and imports

Let `S = LocalFieldTheory.DiscreteValuationField.ValuedExtension` and
`T = Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension`.

| Original declaration | Adapted declaration |
| --- | --- |
| `S.ramificationIndex_ne_zero`, M343.002, lines 54–59 | `T.ramificationIndex_ne_zeroStatement` |
| `S.ramificationIndex_pos`, M343.003, lines 65–70 | `T.ramificationIndex_posStatement` |

The source context's `ValuationTheory.DiscreteValuationField.CompleteDVF`
and its `valuation`, `toDVF`, `valuationSubring` and `maximalIdeal` projections
are reused with the `Langlands.NYLL` namespace prefix from the already
published modules. M108.003 is inlined as described above rather than
duplicated. The source proof calls, including M343.003's
`Nat.pos_of_ne_zero`, are removed when forming the proposition definitions.

The source import
`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core`
is replaced by these focused imports:

- `Mathlib.NumberTheory.RamificationInertia.Ramification`, for
  `Ideal.ramificationIdx'`;
- `Mathlib.RingTheory.Valuation.Extension`, for `Valuation.HasExtension`
  and the canonical valuation-subring algebra;
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`,
  for the published complete-DVF package and its canonical projections.

## Attribution and modifications

The paired Lean file retains the original copyright and author header:
copyright 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved; authors
Naganori Yamaguchi (assisted by OpenAI Codex). The source is released under
Apache-2.0. The existing Library
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Neither selected source file has a source-specific entry in the retained
NOTICE or the supplement's ValuedFieldTheory attribution, notice and source
tables.

Worker 308 supplied the shared revision-2 design for these two targets.
Worker 192 checked it against the original sources and published projection
modules, retained its target bodies and telescope, expanded this source
correspondence, and prepared the focused submission on 13 November 2026.
The complete changes are extraction of M343.002–003; the namespace prefix;
replacing each theorem by a `def` with suffix `Statement` and codomain
`Prop`; removing its proof; inlining M108.003's exact Mathlib body and
omitting redundant type annotations; replacing the import as listed above;
and adding descriptive documentation and this modification record.
