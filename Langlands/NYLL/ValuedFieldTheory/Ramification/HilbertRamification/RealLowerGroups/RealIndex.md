# Real indices for the chosen maximal-ideal filtration

This module extracts M304.004, `realRamificationExponent`, and M304.009,
`realRamificationIdeal`, from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L103-L140),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The selected source
definitions occupy lines 103–109 and 137–140, including their docstrings.
The complete original file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.

The source is retained under registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source path
above. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the project, workspace or current
Library errata lookup. The source partition records no patch10 change to
this file.

## Names, full telescopes and bodies

Both declarations belong to
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`.
They preserve the original names with the `Langlands.NYLL` prefix.
Their full telescopes and bodies, with that namespace open, are:

```lean
noncomputable def realRamificationExponent (s : ℝ) : ℕ :=
  (Int.ceil (s + 1)).toNat

noncomputable def realRamificationIdeal.{w, x}
    {L : Type w} [Field L]
    (target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (s : ℝ) : Ideal target.valuationSubring :=
  target.maximalIdeal ^ realRamificationExponent s
```

In the Lean file, a surrounding `noncomputable section` supplies the
noncomputability annotation. The exponent has no universe, field, valuation
or typeclass parameters: its only argument is the explicit real number `s`.
The ideal has implicit field type `L`, a supplied field instance, explicit
chosen DVF `target` and explicit real index `s`. The universes `w` and `x`
are independent: `L : Type w` and `target.ValueGroup : Type x`.
The valuation ring remains in `Type w`.

The definitions use no base field, algebra structure, valuation-extension
instance or uniqueness hypothesis. They also use no finite-dimensionality,
separability, completeness or Galois assumptions. The source section
introduces such base and extension parameters at lines 98–101, but they do
not occur in the actual telescopes of these two definitions.

## Actual ring, ideal and indexing convention

The imported module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`
supplies the chosen `DVF` bundle and its existing abbreviations.
`target.valuationSubring` is the type underlying the actual subring
`target.valuation.valuationSubring` of `L`; its elements satisfy
`target.valuation z ≤ 1`. Its ring and local-ring structures are the
canonical Mathlib structures inherited from that valuation subring.
`target.maximalIdeal` is exactly
`IsLocalRing.maximalIdeal target.valuationSubring`.
Thus `realRamificationIdeal target s` is an ideal of this chosen ring,
using the ordinary Mathlib natural power of this actual maximal ideal.
No new valuation normalization, ring, ideal or abstract filtration is chosen.

`Int.ceil` first takes the least integer greater than or equal to `s + 1`.
`Int.toNat` then sends a nonpositive integer to zero and a positive integer
to the corresponding natural number. Consequently the formula truncates
the exponent at zero: for `s ≤ -1` the exponent is zero, while for
`s ≥ -1` it is the nonnegative ceiling of `s + 1`. At a natural index
`n : ℕ`, viewed in `ℝ`, the exponent is `n + 1`. The ideal formula therefore
represents the maximal-ideal filtration with term
`target.maximalIdeal ^ (n + 1)` at natural index `n`, extended constantly
by the zeroth ideal power, the whole valuation ring, below `-1`.

These observations explain the mathematical meaning of the formulas.
This module contains only the two data definitions; it does not formally
prove their special values or monotonicity. The source property theorems
M304.005–.008 and M304.010–.013 are separate statement and proof units.
The source-order `.END` scheduling entries between the two selected
definitions are not dependencies of these definition bodies.

## Source correspondence and modifications

| Original source | Adaptation |
| --- | --- |
| Namespace at lines 91–94 | Prefix `RamificationTheory.HilbertRamification.Higher` with `Langlands.NYLL`. |
| M304.004 at lines 103–109 | Preserve `realRamificationExponent` and its body `(Int.ceil (s + 1)).toNat`; replace its docstring with a concise description. |
| M304.009 at lines 137–140 | Preserve `realRamificationIdeal`, its actual chosen valuation-ring codomain and its maximal-ideal-power body; spell out the implicit `L` and supplied `[Field L]`. |
| Source section at lines 98–101 | Omit unused base, algebra and extension parameters; retain independent target universes `w` and `x`. |
| Source imports at lines 7–10 | Import the published DVF data module, Mathlib's real Archimedean/floor-ring module and ideal operations. Omit valuation-extension and Galois imports. |
| Other declarations | Exclude their statements, proofs and data constructions from this unit. |

The module introduces no valuation-ring automorphism, lower or upper
ramification subgroup, Herbrand function, inertia assertion or reciprocity
clause. In particular, it does not import or depend on the pending proof
of M304.003.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing copies of
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
The supplement's `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md`
lists four other valuation-theory files, with no entry for
`RealLowerGroups.lean`; the inherited notices and earlier-source credits
remain preserved in the existing NOTICE.

Worker 106 supplied the source extraction, parameter analysis and grouping
of these two definitions in the task contract. Worker 60 independently
checked the selected original and published dependency, implemented the
extraction, reduced the imports and wrote this documentation on
1 November 2026. The Lean header records the modifications.
