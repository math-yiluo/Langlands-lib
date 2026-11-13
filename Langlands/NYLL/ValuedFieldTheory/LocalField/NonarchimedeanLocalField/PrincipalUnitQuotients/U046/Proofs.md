# The trivial successive principal-unit class

This module proves
`Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_eq_one_iff`,
the proof phase of M132.046 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published target
`Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_eq_one_iffStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem principalUnitsSuccQuotMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    principalUnitsSuccQuotMk_eq_one_iffStatement K n u
```

The parameters are the target's parameters in the target's order: the field
`K` in an arbitrary universe `u`, its `Field` and `ValuativeRel` instances,
an arbitrary natural depth `n` (including `0`) and an element `u` of the
principal-unit subgroup `principalUnits K n` of `𝒪[K]ˣ`. The target unfolds
to

```lean
principalUnitsSuccQuotMk K n u = 1 ↔
  u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)
```

so the class of `u` in `U^n/U^(n+1)` is trivial exactly when `u` lies in
the embedded subgroup `U^(n+1)`. No hypothesis is added.

The imported definitions are used unchanged: `PrincipalUnitsSuccQuot K n`
is the quotient group of `principalUnits K n` by the embedded subgroup
`N = (principalUnits K (n + 1)).subgroupOf (principalUnits K n)`, with the
quotient's own commutative group structure; `principalUnitsSuccQuotMk K n`
is `QuotientGroup.mk' N`; and `principalUnitsSuccQuotConcreteEquiv K n` is
`MulEquiv.refl` between the named quotient and the concrete quotient.

## Implemented proof

The proof first states the unfolded iff with `show`, a definitional
unfolding of the target, and splits it with `constructor`.

- Forward: given `h : principalUnitsSuccQuotMk K n u = 1`, applying the
  forward direction of Mathlib's `QuotientGroup.eq_one_iff`
  (`Mathlib/GroupTheory/QuotientGroup/Defs.lean`) reduces the goal to
  `(u : principalUnits K n ⧸ N) = 1`. The proof forms
  `h' := congrArg (principalUnitsSuccQuotConcreteEquiv K n) h` and closes
  the goal with `exact h'`; the two sides agree by definitional unfolding of
  the quotient map and of the reflexive equivalence.
- Backward: given `h : u ∈ N`, injectivity of
  `principalUnitsSuccQuotConcreteEquiv K n` reduces the goal to equality of
  the images of the two classes, which is closed by
  `exact (QuotientGroup.eq_one_iff u).mpr h`, again by definitional
  unfolding.

No auxiliary declaration is introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 654–670](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L654-L670):
the docstring at 654, the theorem telescope and conclusion at 655–659 and
the proof at 659–670 (the task's unit range 655–673 ends before the next
declaration). The complete retained original file has SHA-256
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.principalUnitsSuccQuotMk_eq_one_iff` | `Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_eq_one_iff` |
| Its statement | Published `principalUnitsSuccQuotMk_eq_one_iffStatement` |

Modifications by Worker 147 on 13 November 2026:

- add the `Langlands.NYLL` namespace prefix; give the theorem the published
  target applied to its parameters as its type and add the leading `show`;
- replace the closing `simpa using h'` of the forward direction by
  `exact h'`, and the closing `simpa using (QuotientGroup.eq_one_iff u).mpr h`
  of the backward direction by `exact (QuotientGroup.eq_one_iff u).mpr h`.
  The original steps fail in the approved Mathlib: there `simp` rewrites
  the goal `(u : principalUnits K n ⧸ N) = 1` to `u ∈ N` and the hypothesis
  `h'` to `principalUnitsSuccQuotMk K n u = 1`, so `simpa` reports a type
  mismatch; in the backward direction it likewise normalizes the goal and
  the supplied term to `principalUnitsSuccQuotMk K n u = 1` and `u ∈ N`.
  Without simplification, the terms already have the goals' types up to
  definitional unfolding, so `exact` accepts them. The surrounding proof
  structure (`constructor`, the `apply` steps, `congrArg` and the injectivity
  reduction) is unchanged;
- replace the source imports by the single import of the statement module;
  omit the source `noncomputable section`, `open Filter` and all other
  source declarations.

The theorem name, docstring and telescope are unchanged. The partition
records no patch10 change to this module.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`,
which supplies the target and, through
`...PrincipalUnitQuotients.SuccessorDefinitions`, the quotient, quotient map
and concrete equivalence described above, together with Mathlib's
`Mathlib.GroupTheory.QuotientGroup.Basic`. That module and everything it
imports are left unchanged.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", released under Apache-2.0. The Lean file carries the dated
modification record. The retained original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). No
errata note for either source ID exists in the project or Library `notes/`.
The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
selected source file is not among the third-party paths listed in the
NOTICE. Worker 147 adapted this proof directly from the pinned original; no
other worker's draft is reused. The statement and definitions are Worker
211's, used unchanged.

This module proves only the stated triviality test; the kernel description
M132.041 and the quotient comparisons are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. The source proof steps, with only the leading `show` added,
were also compiled in a private check (diagnostic
`e495da85-646c-4ec2-8134-f2ac1f34a6c5`) and failed with exactly the two
`simpa` type mismatches described above. These are development checks, not exact-target validation or
independent acceptance.
