# NYLL M351.012–M351.016: targets for the linear model of `e(X_i)`

This module states five theorems of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization` as
Prop-valued targets. These are the source-private theorems that directly
follow the linear model `linearInVariableStabilization π i = C π * X_i`
(M351.011, published as `Langlands.NYLL.PortInternal.M351.d011`):

- the linear model has zero constant coefficient;
- the linear model admits substitution;
- both `ebar(X_i)` and the linear model have order at least one;
- `ebar(X_i)` agrees with its linear model up to order two.

Nothing is proved here. Each target `d01kStatement` is to be proved later as
the theorem `Langlands.NYLL.PortInternal.M351.d01k`.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
lines 405–479. The source-file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
A readable copy of the original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

The source statements, without their proofs, are

```lean
omit [Fintype σ] in
private theorem linearInVariableStabilization_constantCoeff
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff
        (linearInVariableStabilization π i) = 0

omit [Fintype σ] in
private theorem linearInVariableStabilization_hasSubst [Finite σ]
    (π : F.valuationSubring) :
    MvPowerSeries.HasSubst
      (linearInVariableStabilization (σ := σ) π)

omit [Fintype σ] in
private theorem one_le_order_inVariable_stabilization
    (ebar : LubinTateSeries F π) (i : σ) :
    (1 : ℕ∞) ≤ (inVariable ebar i).order

omit [Fintype σ] in
private theorem one_le_order_linearInVariableStabilization
    (π : F.valuationSubring) (i : σ) :
    (1 : ℕ∞) ≤ (linearInVariableStabilization π i).order

omit [Fintype σ] in
private theorem two_le_order_inVariable_sub_linearInVariableStabilization
    (ebar : LubinTateSeries F π) (i : σ) :
    (2 : ℕ∞) ≤
      (inVariable ebar i -
        linearInVariableStabilization π i).order
```

They sit in the section context of source lines 28–36 and 68–70: a
`noncomputable section`, `open scoped BigOperators`,
`attribute [local instance] Classical.propDecidable`, universes `u v w`,
namespaces `LubinTate.SameUniformizer`,
`open LocalFieldTheory.DiscreteValuationField`, and

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]
```

## Source correspondence

| Source unit | Original theorem (`LubinTate.SameUniformizer`, private) and lines | Adapted target (Lean lines, docstring included) |
| --- | --- | --- |
| M351.012 | `linearInVariableStabilization_constantCoeff`, 405–413 | `Langlands.NYLL.PortInternal.M351.d012Statement` (47–50) |
| M351.013 | `linearInVariableStabilization_hasSubst`, 415–421 | `Langlands.NYLL.PortInternal.M351.d013Statement` (52–56) |
| M351.014 | `one_le_order_inVariable_stabilization`, 423–428 | `Langlands.NYLL.PortInternal.M351.d014Statement` (58–61) |
| M351.015 | `one_le_order_linearInVariableStabilization`, 430–435 | `Langlands.NYLL.PortInternal.M351.d015Statement` (63–66) |
| M351.016 | `two_le_order_inVariable_sub_linearInVariableStabilization`, 437–479 | `Langlands.NYLL.PortInternal.M351.d016Statement` (68–72) |

Names resolve as follows:

- `linearInVariableStabilization` is the published M351.011 definition
  `Langlands.NYLL.PortInternal.M351.d011`, which has the same type and body.
- `LocalField` and `F.valuationSubring` are the published
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K`
  and its accessor (M334.001, M334.003).
- `LubinTateSeries F π` is the published
  `Langlands.NYLL.LubinTate.LubinTateSeries F π`.
- `inVariable` is the published M348.001
  `Langlands.NYLL.LubinTate.SameUniformizer.inVariable`.
- `MvPowerSeries.constantCoeff`, `MvPowerSeries.HasSubst` and
  `MvPowerSeries.order` are Mathlib's.

**Binders.** Every source theorem begins with `omit [Fintype σ] in`, so the
section instance `[Fintype σ]` is not a parameter of any of them. In M351.012,
M351.013 and M351.015 the explicit binder `(π : F.valuationSubring)` shadows
the section variable `{π}`. M351.014 and M351.016 use the section `{π}`
through `ebar : LubinTateSeries F π`, and M351.016 also uses it in
`linearInVariableStabilization π i`. M351.013 adds its own `[Finite σ]`.

The adapted module declares the section variables
`{K : Type u} [Field K]`, `{F : LocalField.{u, v} K} {π : F.valuationSubring}`
and `{σ : Type w}`, with no `Fintype σ`. Each target then repeats the explicit
and instance binders of its source theorem. A private probe rebuilt the source
section verbatim, with the private source definition and the published
`LocalField`. In it, `#check` printed these telescopes:

- `d012Statement : {K : Type u} → [Field K] → {F : LocalField K} → {σ : Type w} → F.valuationSubring → σ → Prop`;
- `d013Statement : {K} → [Field K] → {F} → {σ} → [Finite σ] → F.valuationSubring → Prop`;
- `d014Statement : {K} → [Field K] → {F} → {π : F.valuationSubring} → {σ} → LubinTateSeries F π → σ → Prop`;
- `d015Statement : {K} → [Field K] → {F} → {σ} → F.valuationSubring → σ → Prop`;
- `d016Statement : {K} → [Field K] → {F} → {π} → {σ} → LubinTateSeries F π → σ → Prop`.

These are the elaborated binders of the source theorems, in the same order and
with the same binder kinds. No common finite-variable premise is imposed:
only M351.013 has `[Finite σ]`, as in the source, and no target has
`Fintype σ`. The universes of `K`, of the value group of `F` and of `σ` are
independent. The element `π` is arbitrary in `F.valuationSubring`. No
uniformizer hypothesis is added.

**Bodies.** Each body is the source conclusion verbatim, with
`linearInVariableStabilization` replaced by `d011`. In the same probe,
`@linearInVariableStabilization.{u, v, w} = @d011.{u, v, w}` holds by `rfl`.
After rewriting with this equation, each `d01kStatement …` equals the source
conclusion stated in the source section by `with_reducible rfl`. For M351.014
this needs no rewrite, because its statement does not mention the
definition. The source's local instance
`Classical.propDecidable` is omitted because no statement type involves a
decidability instance. The reducible comparison above was made with that
instance active in the source section.

## Mathematical meaning

Write `O = F.valuationSubring`, let `π ∈ O`, `i : σ`, and let
`ebar : LubinTateSeries F π`, a power series in `O⟦X⟧` with zero constant
coefficient and linear coefficient `π`. Write `ebar(X_i)` for
`inVariable ebar i`, i.e. `PowerSeries.subst (MvPowerSeries.X i) ebar`, and
`π·X_i` for `d011 π i = C π * X_i`. For a multivariable series `f`,
`MvPowerSeries.order f : ℕ∞` is the least total degree of a monomial with a
nonzero coefficient in `f` (and `⊤` for `f = 0`).

- **M351.012**, `d012Statement π i`:
  `MvPowerSeries.constantCoeff (d011 π i) = 0`. The series `π·X_i` has zero
  constant coefficient.
- **M351.013**, `d013Statement (σ := σ) π`, for finite `σ`:
  `MvPowerSeries.HasSubst (d011 (σ := σ) π)`. The family `i ↦ π·X_i` can be
  substituted into multivariable series over `σ`. In Mathlib this means each
  member has nilpotent constant coefficient and, for each exponent, only
  finitely many members have a nonzero coefficient there.
- **M351.014**, `d014Statement ebar i`:
  `(1 : ℕ∞) ≤ (inVariable ebar i).order`. The series `ebar(X_i)` has no
  constant term.
- **M351.015**, `d015Statement π i`: `(1 : ℕ∞) ≤ (d011 π i).order`. The
  series `π·X_i` has no constant term.
- **M351.016**, `d016Statement ebar i`:
  `(2 : ℕ∞) ≤ (inVariable ebar i - d011 π i).order`, where `π` is the linear
  coefficient of `ebar` (the implicit parameter in its type). The
  coefficients of `ebar(X_i)` and `π·X_i` agree in total degree below two:
  both vanish in degree zero, and at the exponent `X_i` both are `π`. So
  `π·X_i` is the linear model of `ebar(X_i)`.

The later source units of the module use these facts to compare
substitutions into `ebar(X_i)` with substitutions into the linear model.

## Using the later proofs

The targets are reducible `abbrev`s, so a proof
`theorem d012 (π : F.valuationSubring) (i : σ) : d012Statement π i` can be
used like the source theorem. The same private probe compiled the
following uses of such a proof:

- direct term use where the source proposition is expected, e.g.
  `MvPowerSeries.hasSubst_of_constantCoeff_zero (d012 π)` as a proof of
  `d013Statement (σ := σ) π`, and
  `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (d012 π i)` as a proof
  of `d015Statement π i`, as in the source proofs of M351.013 and M351.015;
- `rw [d012 π i]` and `simp only [d012]`, which rewrite
  `MvPowerSeries.constantCoeff (d011 π i)` to `0`;
- `simp only [d012Statement] at h`, which turns a hypothesis
  `h : d012Statement π i` into the underlying equation.

To prove a target, it is convenient to start with `show` and the underlying
proposition. For example, the source proof of M351.012, with `d011` in place
of `linearInVariableStabilization`, closes `d012Statement π i` after
`show MvPowerSeries.constantCoeff (d011 π i) = 0`.

The explicit arguments of `d013Statement π` do not mention `σ`. A proof that
states it must therefore name the variable type, as in
`d013Statement (σ := σ) π`, just as the source writes
`linearInVariableStabilization (σ := σ) π`. Uses of the proof at an expected
`MvPowerSeries.HasSubst (d011 (σ := σ) π)` infer `σ` from that type.

## Dependencies

The module imports

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Definitions`
  (M351.011, `d011`);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`
  (M348.001 `inVariable`; through its imports also `LubinTateSeries`,
  `LocalField` and `MvPowerSeries.HasSubst`); and
- `Mathlib.RingTheory.MvPowerSeries.Order` (`MvPowerSeries.order`).

The source imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`
and `Mathlib.RingTheory.MvPowerSeries.Trunc`. The focused check of this module
shows that the three imports above suffice for the statements.

## Modifications

All modifications were made by Worker 491 on 14 November 2026:

1. each of the five source theorems is replaced by a Prop-valued `abbrev`
   named `Langlands.NYLL.PortInternal.M351.d01kStatement`. Its binders are
   the elaborated binders of the source theorem, and its body is the source
   conclusion. The `private` modifiers and the source proofs are omitted;
2. the source-private `linearInVariableStabilization` is referred to by its
   published name `d011`;
3. the opened namespaces are written with the `Langlands.NYLL` prefix, and
   `Langlands.NYLL.LubinTate` and `Langlands.NYLL.LubinTate.SameUniformizer`
   are opened so that `LubinTateSeries` and `inVariable` resolve as in the
   source;
4. the section variable `[Fintype σ]` is not declared, since every source
   theorem here omits it. The per-theorem `omit [Fintype σ] in` lines are
   therefore unnecessary and are dropped;
5. the source imports are replaced by the three focused imports above. The
   `noncomputable section`, `open scoped BigOperators`, the local instance
   `Classical.propDecidable` and all other source declarations are omitted;
6. a modification notice in the header, a new module docstring and
   declaration docstrings naming the targeted source units are added.

## License

The original 2026 copyright, Apache-2.0 release line and author header are
preserved verbatim. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
