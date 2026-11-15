# NYLL M349.004: reduction of a series evaluated at inserted Lubin--Tate series

This module proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.map_subst_inVariablesStatement` by
the theorem `Langlands.NYLL.LubinTate.SameUniformizer.map_subst_inVariables`.
It imports two published modules, neither of which is changed:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements`
  (the target);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst`
  (M348.003, `inVariable_hasSubst`).

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.LubinTate.SameUniformizer`
and has the target's exact telescope: implicit `K : Type u` with
`[Field K]`, implicit `F : LocalField.{u, v} K`, implicit
`π : F.valuationSubring`, implicit `σ : Type w` with `[Finite σ]` (instead of
`[Fintype σ]`, as in the source's `omit [Fintype σ] in`), and the explicit
arguments `(ebar : LubinTateSeries F π)` and
`(H : MvPowerSeries σ F.valuationSubring)`. Its type is
`map_subst_inVariablesStatement ebar H`, which unfolds to

```lean
MvPowerSeries.map F.residueMap
    (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H) =
  MvPowerSeries.expand (Nat.card F.residueField)
    (Nat.ne_of_gt Nat.card_pos)
    (MvPowerSeries.map F.residueMap H)
```

Here `inVariable ebar i` is `ebar(X_i)`, and Mathlib's
`MvPowerSeries.expand q hq f` replaces every variable `X_i` of `f` by
`X_i ^ q`. Mathematically: reduction modulo the maximal ideal commutes with
multivariable substitution, and each `ebar(X_i)` reduces to `X_i ^ q` with
`q = Nat.card F.residueField`; hence `H(ebar(X_1), …)` reduces to
`Hbar(X_1 ^ q, …)`. No hypothesis on `H` and no uniformizer hypothesis is
used; finiteness of `σ` is needed for the substitution to be defined.

## Implemented proof

1. `show _ = _` unfolds the reducible target to the displayed equation.
2. `rw [MvPowerSeries.map_subst (inVariable_hasSubst ebar) H]` uses the
   published M348.003 theorem (the family `i ↦ ebar(X_i)` admits
   substitution; its target is a reducible `abbrev`, so it is accepted as the
   `HasSubst` argument) and Mathlib's `MvPowerSeries.map_subst` to move the
   reduction inside: the left side becomes
   `(map F.residueMap H).subst (fun i ↦ map F.residueMap (inVariable ebar i))`.
3. `simp_rw [map_inVariable_for_subst]` rewrites each reduced
   `inVariable ebar i` under the binder to `X_i ^ q`.
4. `rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]` unfolds
   Mathlib's `expand q hq` as `substAlgHom (HasSubst.X_pow hq)`, the
   substitution algebra map of the family `i ↦ X_i ^ q`, and its application
   as `subst`, after which both sides agree syntactically and `rw` closes the
   goal.

The private theorem `map_inVariable_for_subst` has exactly the statement of
M349.002 (`map_inVariableStatement e i`, written out) and repeats the source
M349.002 proof (source lines 67–75): `PowerSeries.HasSubst.X i` over the
valuation subring and over the residue field, then
`rw [inVariable, PowerSeries.map_subst hX e.toPowerSeries,
e.map_residue_eq_frobenius, MvPowerSeries.map_X, PowerSeries.subst_pow hXbar,
PowerSeries.subst_X hXbar]`. It is private because the public M349.002
theorem `map_inVariable` is a separate candidate of the same task still
awaiting publication; this keeps this candidate dependent only on published
modules, as Task 6750 permits, and adds no second public theorem named
`map_inVariable`.

Dependencies: the published definitions `inVariable` and `LubinTateSeries`,
the published theorem `inVariable_hasSubst`, and the Mathlib lemmas named
above. No public auxiliary declaration, instance or simp attribute is added.

## Source and attribution

This is M349.004, theorem `LubinTate.SameUniformizer.map_subst_inVariables`,
lines 94–108 of Naganori Yamaguchi's
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
lists this unit as M349.004. No patch10 edit applies, and no applicable NYLL
erratum was found in the published errata notes.

The implemented proof is the source proof (lines 106–108) preceded by
`show _ = _`, with the source's reference to `map_inVariable` (M349.002)
replaced by the private copy described above.

## Modification record

- Extract M349.004 into this focused module; prefix the namespace with
  `Langlands.NYLL`.
- Import the published Reduction statement module and the published M348.003
  proof module instead of the source imports.
- State the conclusion as the published target
  `map_subst_inVariablesStatement ebar H` and unfold it with a leading
  `show _ = _`.
- Declare `σ` without `[Fintype σ]` directly, with `[Finite σ]` on the
  theorem as in the source; the resulting binders are the same.
- Replace the reference to M349.002 by the private
  `map_inVariable_for_subst`, which repeats the source M349.002 proof.
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
no errors or warnings, and the theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. Compilation is not acceptance;
publication requires the Lake build, exact-target and unchanged-statement
checks, independent semantic review and integration.
