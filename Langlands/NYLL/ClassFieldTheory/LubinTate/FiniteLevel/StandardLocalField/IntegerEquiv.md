# Standard integer-ring equivalence (M335.005)

`Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv K` is the ring
equivalence

```
𝒪[K] ≃+* (standardLocalField K).valuationSubring
```

for a field `K : Type` with `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`; `K` is explicit and the four instances are
instance-implicit, exactly as in the source section variables. Here
`𝒪[K]` is Mathlib's scoped `ValuativeRel` notation for the integer subring
`Valuation.integer (ValuativeRel.valuation K)`, and
`(standardLocalField K).valuationSubring` is the valuation-ring type of the
canonical local-field package `Langlands.NYLL.LubinTate.standardLocalField K`
(M335.001), that is, the valuation subring of its chosen valuation
`Valued.v` built from the same valuative relation.

Both functions keep the underlying element of `K`: the forward map sends
`x` to `⟨(x : K), _⟩` and the inverse sends `y` to `⟨(y : K), _⟩`. The two
membership obligations hold because both rings are cut out by the same
inequality `ValuativeRel.valuation K a ≤ 1`. The inverse laws and the
additive and multiplicative laws are `rfl`, as in the source. The axioms used
are only `propext`, `Classical.choice` and `Quot.sound`.

## Source

Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`,
lines 74–89 (declaration at line 76), with section variables at lines 37–38
and `open scoped ValuativeRel` at line 28. Source file SHA-256:
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The upstream development used Lean 4.35.0-rc2; this file is checked in the
approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

| Source (line) | Library |
| --- | --- |
| `LubinTate.standardLocalFieldIntegerEquiv` (76) | `Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv` |
| `LubinTate.standardLocalField` (42), used | `Langlands.NYLL.LubinTate.standardLocalField` (published M335.001) |

## Modifications

- Extraction of this single definition; the namespace `LubinTate` becomes
  `Langlands.NYLL.LubinTate`. Name, type, explicit `K : Type`, all four
  instance hypotheses, the docstring and the bodies of both functions and of
  the four laws are unchanged.
- Proof terms of the two subtype memberships. The source's `toFun`
  obligation changes the goal to `(standardLocalField K).valuation (x : K) ≤ 1`
  and rewrites with the theorem `standardLocalField_valuation_eq` (M335.003);
  its `invFun` obligation changes to `ValuativeRel.valuation K (x : K) ≤ 1`
  and rewrites backwards with the same theorem. Here both obligations change
  the goal directly to `ValuativeRel.valuation K (x : K) ≤ 1` and close it
  with `x.property`. This is the same definitional reduction by which the
  source proves M335.003 (`unfold` and `rfl`), so the construction no
  longer depends on the M335.003 proof, which is not part of this unit. The
  resulting functions are the same: only proofs of propositions differ.
- Imports. The source imports six NYLL modules, including principal-unit,
  Teichmüller, ideal-quotient and open-subgroup APIs used only by later
  declarations of the file. This module imports only the published module
  of `standardLocalField` (M335.001),
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Definitions`,
  which supplies the shared FM `LocalField` package and `localCompleteDVF`.
- The source's unused `open` commands for `LocalFieldTheory`,
  `LocalFieldTheory.DiscreteValuationField`, `...CompleteDVF` and
  `LocalFieldTheory.IsNonarchimedeanLocalField` are omitted; only
  `open scoped ValuativeRel` (for `𝒪[K]`) is kept.
- Replacement module documentation and a modification notice in the header.

The original copyright, Apache-2.0 and author lines are retained;
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
unchanged; NOTICE has no entry specific to this source file.

## Scope

This unit is only the definition. The coercion targets M335.006–007 are in
the paired statement module `IntegerEquivCoeStatements`; the maximal-ideal
transport M335.008–010 and the unit and uniformizer constructions of the
same source file are outside this unit.
