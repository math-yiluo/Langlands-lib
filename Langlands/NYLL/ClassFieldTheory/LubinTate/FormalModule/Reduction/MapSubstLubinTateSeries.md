# NYLL M349.003: reduction of a Lubin--Tate series evaluated at a series

This module proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.map_subst_lubinTateSeriesStatement`
by the theorem
`Langlands.NYLL.LubinTate.SameUniformizer.map_subst_lubinTateSeries`.
It imports three published modules, none of which is changed:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements`
  (the target);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U004.Proofs`
  (M347.004, `HasLinearTerm.constantCoeff_eq_zero`);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U005.Proofs`
  (M347.005, `HasLinearTerm.hasSubst`).

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.LubinTate.SameUniformizer`
and has the target's exact telescope: implicit `K : Type u` with
`[Field K]`, implicit `F : LocalField.{u, v} K`, implicit
`π : F.valuationSubring`, implicit `σ : Type w` with `[Fintype σ]`, the
explicit `e : LubinTateSeries F π`, implicit
`H : MvPowerSeries σ F.valuationSubring` and `L : σ → F.valuationSubring`,
and the explicit hypothesis `hH : HasLinearTerm H L`. Its type is
`map_subst_lubinTateSeriesStatement e hH`, which unfolds to

```lean
MvPowerSeries.map F.residueMap (PowerSeries.subst H e.toPowerSeries) =
  (MvPowerSeries.map F.residueMap H) ^ Nat.card F.residueField
```

Here `HasLinearTerm H L` is the published predicate
`(2 : ℕ∞) ≤ (H - linearForm L).order`: `H` agrees with `∑ L_i X_i` up to
terms of total degree at least two. Mathematically: such an `H` has zero
constant coefficient, so it can be substituted into the one-variable series
`e`; reduction modulo the maximal ideal commutes with this substitution, and
`e` reduces to the Frobenius series `X ^ q` with
`q = Nat.card F.residueField`. Hence `e(H)` reduces to `Hbar ^ q`, where
`Hbar` is the coefficientwise reduction of `H`. No uniformizer hypothesis is
used.

## Implemented proof

1. `show _ = _` unfolds the reducible target to the displayed equation.
2. `hconst : MvPowerSeries.constantCoeff H = 0` is `hH.constantCoeff_eq_zero`
   (published M347.004), whose stated type
   `HasLinearTerm.constantCoeff_eq_zeroStatement hH` is a `def` that the type
   ascription unfolds by definitional unfolding.
3. `hsubst : PowerSeries.HasSubst H` is `hH.hasSubst` (published M347.005),
   ascribed in the same way.
4. `hmap : PowerSeries.HasSubst (MvPowerSeries.map F.residueMap H)` is
   Mathlib's `PowerSeries.HasSubst.of_constantCoeff_zero`, whose hypothesis
   `constantCoeff (map F.residueMap H) = 0` is proved by `simp [hconst]`.
5. One `rw` chain then rewrites
   `PowerSeries.map_subst hsubst e.toPowerSeries` (reduction commutes with
   substitution of `H`), `e.map_residue_eq_frobenius` (the reduced series is
   `X ^ q`), `PowerSeries.subst_pow hmap` and `PowerSeries.subst_X hmap`
   (substituting `Hbar` into `X ^ q` gives `Hbar ^ q`), after which the two
   sides agree syntactically and `rw` closes the goal.

Dependencies: the published definitions `LubinTateSeries` and
`HasLinearTerm` (through the statement module), the published theorems
`HasLinearTerm.constantCoeff_eq_zero` and `HasLinearTerm.hasSubst`, and the
Mathlib lemmas named above. No auxiliary declaration, instance or simp
attribute is added.

## Source and attribution

This is M349.003, theorem `LubinTate.SameUniformizer.map_subst_lubinTateSeries`,
lines 77–92 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source-file SHA-256
is `b9a7d469a06616be19f5841ca96c26f22887650ccf4d83336a84ab89b2ccb2ad`
(recomputed by Worker 465 on 15 November 2026). The retained original is
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The [port partition](../../../../../../notes/reuse/nyll-public-port/m337-m360.md#m349)
lists this unit as M349.003. No patch10 edit applies, and no applicable NYLL
erratum was found in the published errata notes.

The implemented proof is the source proof: the same `hmap` fact and the same
`rw` chain. The source uses `hH.constantCoeff_eq_zero` inside `simp` and
`hH.hasSubst` as an argument of `PowerSeries.map_subst` directly; here they
are first bound with their unfolded types (steps 2 and 3). The published
theorems state their conclusions through `def` targets, which `simp` does not
unfold, so the ascription is needed for `hconst`; the same binding is used for
`hsubst` for uniformity.

## Modification record

- Extract only M349.003 into this focused module; prefix the namespace with
  `Langlands.NYLL`.
- Import the published Reduction statement module and the published M347.004
  and M347.005 proof modules instead of the source imports.
- State the conclusion as the published target
  `map_subst_lubinTateSeriesStatement e hH` and unfold it with a leading
  `show _ = _`.
- Bind `hH.constantCoeff_eq_zero` and `hH.hasSubst` with type ascriptions
  before using them in `simp` and `rw`.
- Append the unit label to the source docstring, and replace the module
  documentation.

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, followed by Worker 465's dated modification
record. The unchanged inherited
[LICENSE](../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library. No published statement or definition is edited.

## Environment

Development environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`): the module compiles with
no errors or warnings. Compilation is not acceptance; publication requires the
Lake build, exact-target and unchanged-statement checks, independent semantic
review and integration.
