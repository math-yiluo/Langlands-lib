# The genuine real lower ramification subgroup

This module defines
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup`
in
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroup`.
It is the subgroup of the actual algebra automorphism group whose
pointwise displacements on the chosen target valuation ring lie in the
published real ramification ideal.

## Full telescope and carrier

The four universes `u, v, w, x` are independent. The complete telescope is:

```lean
{K : Type u} {L : Type w}
[Field K] [Field L] [Algebra K L]
{base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
{target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
[base.valuation.HasExtension target.valuation]
(huniq :
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
    base target)
(s : ℝ) : Subgroup Gal(L/K)
```

The universes `u, w` belong to the field carriers and `v, x` to the chosen
value groups. The existing five-universe uniqueness predicate is used at
precisely `u, v, w, x, x`, so the comparison value group is in `Type x`.
The extension instance uses the algebra map of the supplied `Algebra K L`.
`Gal(L/K)` is Mathlib's notation for `L ≃ₐ[K] L`; the construction requires
no `IsGalois`, finite-dimensionality, separability, completeness or other
mathematical premise.

The carrier is definitionally the set

```lean
{σ | ∀ a : target.valuationSubring,
  valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a - a ∈
    realRamificationIdeal target s}
```

Here `target.valuationSubring` is the actual chosen valuation ring,
the subtype of `L` cut out by `target.valuation z ≤ 1`. The existing
`valuationSubringAutOfUniqueExtension` restricts the supplied `σ` to this
ring. The subtraction and ideal membership in the displayed carrier are
both operations in that same ring, with no replacement of the valuation,
ring, algebra or automorphism group.

The imported real ideal is the ordinary natural ideal power

```lean
realRamificationIdeal target s =
  target.maximalIdeal ^ (Int.ceil (s + 1)).toNat
```

This equality describes its definitional expansion. The index `s` ranges
over all of `ℝ`, with no lower bound. `Int.toNat` truncates nonpositive
ceilings to zero. The implementation uses the existing exponent and ideal
definitions unchanged and does not import their separate monotonicity or
endpoint proofs.

## Implemented subgroup closure proofs

The only new proofs are the three structure fields of the subgroup.
They retain the source proof bodies and reuse the published automorphism
laws under their original short names.

For `one_mem'`, the identity evaluation law reduces the displacement to
`a - a = 0`. The ideal's `zero_mem` proves membership.

For `mul_mem'`, write `eσ` and `eτ` for the actual restricted ring
automorphisms. The displacement identity is

```text
e(σ * τ)(a) - a = eσ(eτ(a) - a) + (eσ(a) - a).
```

The first summand belongs to the ideal because the displacement for `τ`
does and
`valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff`
preserves membership under `eσ`. The second belongs by the displacement
condition for `σ`. The source's `rw` step uses
`valuationSubringAutOfUniqueExtension_mul_apply` and `map_sub`, then
`ring` verifies the additive rearrangement. `Ideal.add_mem` finishes.

For `inv_mem'`, put `b = e(σ⁻¹)(a)` and apply the displacement condition
for `σ` at `b`. The existing
`valuationSubringAutOfUniqueExtension_apply_inv_apply` simplifies this to
`a - b` in the ideal. Its `neg_mem` gives `b - a`, the required displacement
for `σ⁻¹`. The source's simplifications use the published simp laws.

The single import of `ValuationSubringAutProof` supplies all seven
published automorphism laws and the actual definitions in their import
closure. No action instance or ideal-preservation assumption is added.
This unit introduces only the subgroup definition; the public membership,
natural-index, antitone, normality and endpoint properties M304.023–.029
belong to later focused statement and proof units.

## Original-to-adapted declaration map

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 304–368](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L304-L368).
The complete file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
Lines 1–368 were read directly for this adaptation, including the entire
subgroup definition and its prerequisite telescope and automorphism laws.

| Original at the pinned commit | Adapted declaration or reuse |
| --- | --- |
| M304.022, `RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup`, lines 308–368 | `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup`; original short name, carrier and all three subgroup structure proofs retained. |
| Independent universe declaration, line 33; fields, algebra, chosen DVFs and extension, lines 98–101 | Retain `u, v, w, x` and the supplied telescope; omit unused `y`. |
| M304.001 uniqueness predicate, lines 48–52 | Reuse `Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension` at comparison universe `x`. |
| M304.004 exponent, lines 103–109; M304.009 ideal, lines 137–140 | Reuse the published `realRamificationExponent` and `realRamificationIdeal` without changes. |
| M304.014 actual valuation-ring automorphism, lines 164–182 | Reuse the published `valuationSubringAutOfUniqueExtension` unchanged. |
| M304.015–.021 automorphism laws, lines 184–302 | Reuse the published laws by Lean name; the subgroup fields use identity, multiplication, inverse evaluation and real-ideal preservation. |

The source partition records no patch10 modification for M304. Its
source-order dependency markers add no mathematical hypothesis or import.
The existing generic congruence groups and host p-adic ramification groups
use different supplied structures; this extraction directly constructs the
chosen arbitrary-DVF subgroup required here.

## Attribution and modification record

Worker 1199 adapted M304.022 and wrote this Markdown on 1 November 2026.
Worker 106 contributed source extraction, the exact carrier and telescope,
and the subgroup proof-route analysis. Modifications prefix the namespaces
with `Langlands.NYLL`, replace the broad upstream imports with the public
`ValuationSubringAutProof` module and explicit `Mathlib.Tactic.Ring`, and
omit unrelated declarations and unused source context (`y`, the
`noncomputable section` and pointwise scope). The retained definition body,
including all subgroup closure proofs, is unchanged from lines 304–368.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained: copyright 2026
Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The source is Apache-2.0. The existing
verbatim [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
The supplement's ValuedFieldTheory attribution table has no
`RealLowerGroups.lean` entry; the retained NOTICE likewise has no entry for
this file. The workspace, project and current-Library errata directories
were absent when checked.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, distinct from upstream's
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
