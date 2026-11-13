# Additive-valuation restriction targets

This module extracts the conclusions of M345.001–002 from Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationAddVal.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationAddVal.lean#L31-L138),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The two `def` declarations return `Prop`; they provide targets for later
proofs and assert no proof of either proposition.

## Source correspondence

The original namespace of both source theorems is
`LocalFieldTheory.DiscreteValuationField.ValuedExtension`. The adapted
namespace is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension`.
The names in each row are relative to those respective namespaces.

| Source unit | Source declaration lines | Source name | Adapted name |
| --- | --- | --- | --- |
| M345.001 | 39–128; conclusion 41–44 | `addVal_integerMap_eq_ramificationIndex_nsmul` | `addVal_integerMap_eq_ramificationIndex_nsmulStatement` |
| M345.002 | 132–138; conclusion 134–136 | `addVal_integerMap_eq_ramificationIndex_of_irreducible` | `addVal_integerMap_eq_ramificationIndex_of_irreducibleStatement` |

Both retain the complete source telescope from lines 24 and 31–34:

```lean
universe u v w x
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
[base.valuation.HasExtension target.valuation]
```

Here `CompleteDVF` is the published
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`.
The first declaration additionally retains the explicit binder
`(a : base.valuationSubring)`. The second retains the implicit binder
`{a : base.valuationSubring}` and the explicit proof binder
`(ha : Irreducible a)`, even though `ha` is unused in the proposition body.
No finite-dimensionality, module finiteness, module torsion-freeness,
nonzero-element hypothesis, extra value-group parameter or replacement
valuation is introduced.

For `a` in the actual base valuation subring, the first target is

```lean
IsDiscreteValuationRing.addVal target.valuationSubring
    ((algebraMap base.valuationSubring target.valuationSubring) a) =
  (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal) •
    IsDiscreteValuationRing.addVal base.valuationSubring a
```

The scalar is a natural number, acting on `ℕ∞` by natural scalar
multiplication. The explicit `a` ranges over the whole valuation subring,
including zero, whose normalized additive valuation is `⊤`.
The second target has the same left side and right side
`((Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal) : ℕ∞)`,
under the retained irreducibility binder.

## Canonical objects and definitional replacements

The chosen packages, their valuation subrings and their maximal ideals are
the existing published `CompleteDVF` objects. Their forgetful projections use
the path `CompleteDVF → HenselianDVF → DVF` and preserve the chosen valuation.
In particular, `base.toDVF.valuationSubring` and
`base.valuationSubring` are definitionally identical, as are their maximal
ideals, and likewise for `target`.

The source wrappers come from
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean`,
lines 53–67](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean#L53-L67).
This extraction uses their existing Mathlib bodies directly:

| Source expression | Definitionally identical expression in this module |
| --- | --- |
| M108.003: `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF` | `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` |
| M108.005: `ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap base.toDVF target.toDVF` | `algebraMap base.valuationSubring target.valuationSubring` |

`Valuation.HasExtension` supplies the canonical algebra structure between
these valuation subrings. `Ideal.ramificationIdx'` is computed for their
actual canonical maximal ideals and this same algebra structure.
Both conclusions are therefore definitionally the source conclusions
under the displayed replacements. Neither M108 wrapper is defined or
imported by this extraction.

## Imports and modifications

The original two NYLL imports are replaced by:

- `Mathlib.NumberTheory.RamificationInertia.Ramification`, providing the
  canonical ideal ramification index and its dependencies.
- `Mathlib.RingTheory.Valuation.Extension`, providing the valuation
  extension and canonical valuation-subring algebra.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`,
  providing the published chosen complete-DVF projections and their
  discrete valuation ring instances through its imports.

Worker 308 prepared the focused design in parent Task 5888 draft revision 2
on 13 November 2026. The design extracts these two conclusions, prefixes the
namespace by `Langlands.NYLL`, replaces each `theorem` by a `def` suffixed
`Statement`, applies the two definitional replacements above, reduces the
imports, merges the nested namespace openings and adds descriptive
docstrings. The unused-variable linter is disabled only on the second
definition so that its explicit source proof binder `ha` is retained.
The original proofs and the third source theorem M345.003 are omitted.
No global instance is introduced.

Worker 233 prepared this focused publication on 13 November 2026 from that
shared design, normalized whitespace, read the full original files,
verified the source correspondence, corrected the second declaration's
full source extent to line 138, and expanded this paired documentation.
These are statement targets; the original proofs and the parent's private
proof probes are not part of this module.

## Source provenance and attribution

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The complete original files were read. Their SHA256 values are:

| Original file | SHA256 |
| --- | --- |
| `RamificationAddVal.lean` | `2ea61168d1ded6e730b379aab307057614d161740a64c6dfbfe9b7c0e2f147f6` |
| `Extensions.lean` | `e8999a99fc7ff6c38bd68742b9c7779decfbb2d042f60779bd2386d7950232b5` |

No matching source-specific erratum was found in the Library's
`notes/errata` when preparing this extraction.
The original Apache-2.0 copyright and author text is retained in the Lean
header. The inherited
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged.
Their SHA256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Neither selected original file has an additional source-specific NOTICE
entry.
