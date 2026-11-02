# Normalized Herbrand functions of a normal subgroup filtration

This module extracts exactly M303.003, M303.004 and M303.013 from
Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L48-L119),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The three definitions
are at lines 48–49, 52–53 and 112–119. The complete original file has
SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
Source lines 1–119, including the surrounding section and intervening
theorems, were read for this extraction.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source path
above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the workspace, project or supplied
Library errata lookup. The public declaration partition identifies the
source module as M303 and records no patch10 change.

## Complete interfaces and defining expressions

All three declarations lie in
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
With this namespace open, their complete interfaces and bodies are:

```lean
noncomputable def herbrandSlope
    {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (i : ℕ) : ℝ :=
  (Nat.card (F.lower (i + 1)) : ℝ) / Nat.card (F.lower 0)

noncomputable def herbrandValueNat
    {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (herbrandSlope F) i

noncomputable def herbrandFunction
    {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (s : ℝ) : ℝ :=
  if 0 ≤ s then
    let m := ⌊s⌋₊
    (herbrandValueNat F) m +
      (s - (m : ℝ)) * (herbrandSlope F) m
  else
    s
```

The universe `u` is arbitrary. In each declaration `G` is implicit,
`Group G` is a supplied instance, and both `F` and its index or real
argument are explicit. Their respective function types after `F` are
`ℕ → ℝ`, `ℕ → ℝ` and `ℝ → ℝ`. There are no further parameters.
The subgroup family is exactly `F.lower` from the published
[`AntitoneNormalSubgroupFiltration`](../../GaloisValuation/RamificationQuotients/Filtration.md).
The definitions use the actual Mathlib subgroup carrier types and
`Nat.card`; no replacement cardinal sequence or enumeration is supplied.

The slope is normalized by the cardinality at index zero and shifted
to use the subgroup at `i + 1`. In particular, the affine expression on
the first positive unit interval uses `|F.lower 1| / |F.lower 0|`.
It does not substitute the older unshifted `herbrandStep`.
The prefix sum ranges over exactly the natural indices `i < n`;
the empty prefix is the ordinary empty finite sum.

The nonnegative branch uses natural floor `⌊s⌋₊`, namely `Nat.floor s`.
Thus its local index `m` has type `ℕ`, and the fractional coordinate is
`s - (m : ℝ)`. The test is `0 ≤ s`, so zero belongs to this branch.
The other branch returns `s` itself for every negative real, including
those below `-1`. No integer floor or truncation at `-1` is used.

## Definition scope

These are noncomputable data definitions for every group and every
supplied antitone normal subgroup filtration. They require neither
`Finite G` nor `Fintype G`, no local subgroup `Fintype` or membership
decision instance, no arithmetic extension, no chosen enumeration,
and no eventual-triviality cutoff. The generic filtration itself
contains no termination condition.

Mathlib's `Nat.card` is defined for every type and is zero on infinite
types; real division is also defined at a zero denominator. Consequently
the expressions remain defined without finiteness. This scope alone
does not assert positive slopes, strict monotonicity, surjectivity,
continuity or an inverse. Positivity and inverse properties require
separate results with their appropriate hypotheses.

The existing `Langlands.Ramification.Herbrand.polygon` is a finite
ramp sum with a cutoff; its equality with a floor formula requires an
eventual-one tail for the cardinal sequence.
`Langlands.Ramification.Padic.herbrandPhi` specializes that construction
to actual p-adic lower groups using a proved termination result.
An arbitrary antitone normal filtration can remain constant at a
nontrivial subgroup, so these constructions do not supply the
unrestricted interface here. This module reuses Mathlib's cardinality,
finite sums and natural floor directly.

## Exact source map and modifications

In the table, `S` denotes the original namespace
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`
and `T` denotes
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
Only these prefixes are abbreviated:

| Source declaration | Adapted declaration |
| --- | --- |
| `S.herbrandSlope` (M303.003, lines 48–49) | `T.herbrandSlope` |
| `S.herbrandValueNat` (M303.004, lines 52–53) | `T.herbrandValueNat` |
| `S.herbrandFunction` (M303.013, lines 112–119) | `T.herbrandFunction` |

All three definition bodies and their individual source docstrings are
preserved verbatim. The namespace gains `Langlands.NYLL`.
The original arithmetic `Ramification` import is replaced by the
published generic-filtration module.
`Mathlib.SetTheory.Cardinal.Finite`, `Mathlib.Algebra.Order.Floor.Ring`
and `Mathlib.Algebra.Order.Archimedean.Real.Basic` are retained.
`Mathlib.Algebra.BigOperators.Group.Finset.Basic` and an explicit
`open scoped BigOperators` provide the finite-sum notation.
The two source topology imports are omitted because these definitions
need no analytic theorem.

The unused ambient `[Finite G]` is omitted. It was present in the
original section, but does not occur in the inferred interfaces of
these definitions: their bodies use no finite-group instance.
The source local subgroup instances M303.001–.002 and the redundant
`noncomputable section` are omitted; each definition retains its own
`noncomputable` modifier. No instance is added in this module.
The interleaved theorem commands M303.005–.012 are not dependencies
of the third definition and are omitted.

The unit contains exactly these three definitions and their
implementation. Elementary proposition targets and proofs, the inverse
Herbrand function, an order isomorphism, arithmetic M305 wrappers, upper
groups and inertia or reciprocity results belong to separate units.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are byte-identical to
the pinned originals, with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The root NOTICE third-party inventory has no entry for this source file;
its inherited notices and earlier-source credits remain preserved.

Worker 106 supplied the source extraction, inferred-interface and reuse
analysis in the task contract. Worker 60 independently checked the
original source and existing constructions, implemented the focused
extraction, reduced the imports, and wrote this documentation on
1 November 2026. The Lean header records these modifications.
