# NYLL M349.002–M349.006: reduction of an intertwining defect, targets

This module states five Prop-valued targets. They are exactly the theorems
M349.002–M349.006 of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction`:

- reduction of `e(X_i)` to the residue field is `X_i ^ q`;
- the reduced left side `e(H)` of the intertwining equation is `Hbar ^ q`;
- the reduced right side `H(ebar(X_i))` is the expansion `Hbar(X_i ^ q)`;
- the same-uniformizer intertwining defect reduces to zero;
- every coefficient of the defect is divisible by the chosen uniformizer.

Nothing is proved here. Each target will be proved later by a theorem with
the source name, which is the target name without the `Statement` suffix.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`, lines 57–133.
The source-file SHA-256 is
`b9a7d469a06616be19f5841ca96c26f22887650ccf4d83336a84ab89b2ccb2ad`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence

All names below are in the namespace `LubinTate.SameUniformizer` in the
source and `Langlands.NYLL.LubinTate.SameUniformizer` here.

| Source unit | Original theorem and lines (statement; proof) | Adapted target (Lean lines) |
| --- | --- | --- |
| M349.002 | `map_inVariable`, `omit [Fintype σ] in`, 61–66; 67–75 | `map_inVariableStatement` (48–54) |
| M349.003 | `map_subst_lubinTateSeries`, 77–85; 86–92 | `map_subst_lubinTateSeriesStatement` (56–65) |
| M349.004 | `map_subst_inVariables [Finite σ]`, `omit [Fintype σ] in`, 94–105; 106–108 | `map_subst_inVariablesStatement` (67–78) |
| M349.005 | `map_defect_eq_zero`, 110–115; 116–119 | `map_defect_eq_zeroStatement` (80–86) |
| M349.006 | `uniformizer_dvd_coeff_defect`, 121–129; 130–133 | `uniformizer_dvd_coeff_defectStatement` (88–96) |

M349.001 (`mvPowerSeries_expand_natCard`, source lines 32–55) is not part of
this module. Its target `mvPowerSeries_expand_natCardStatement` is the
accepted sibling module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.ExpandNatCardStatement`.

The section context of source lines 25, 30 and 57–59 is kept: universes
`u v w`, `open LocalFieldTheory.DiscreteValuationField`, and the section
variables

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]
```

The source instance changes are kept as well:

- M349.002 has `omit [Fintype σ] in` and no finiteness hypothesis on `σ`.
- M349.004 has `omit [Fintype σ] in` and the binder `[Finite σ]` in place of
  `Fintype`.
- M349.003, M349.005 and M349.006 use the section instance `[Fintype σ]`.
  `HasLinearTerm` requires it, because its linear form `∑ i, C (L i) * X i` is a
  finite sum.

The constants resolve to published definitions:

- `LocalField` is
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`.
  `F.valuationSubring`, `F.residueField` and `F.residueMap` are its reducible
  abbreviations for the valuation ring `O`, the finite residue field `k` and
  the residue ring map `O →+* k` of `F.toCompleteDVF`.
- `LubinTateSeries F π` is `Langlands.NYLL.LubinTate.LubinTateSeries F π`.
- `inVariable` and `defect` are the published M348.001 and M348.005
  definitions.
- `HasLinearTerm` is the published M347 definition in
  `Langlands.NYLL.LubinTate.SameUniformizer`.

Each target is an `abbrev`. Its parameters are the complete parameter list of
the source theorem, in source order and with the same binder kinds, and its
body is the source conclusion verbatim. A private `#check` probe with
`pp.universes` prints these telescopes, abbreviating `F.valuationSubring` as
`O`:

- `map_inVariableStatement : {K : Type u} → [Field K] → {F : LocalField.{u,v} K} → {π : O} → {σ : Type w} → LubinTateSeries F π → σ → Prop`;
- `map_subst_lubinTateSeriesStatement : {K} → [Field K] → {F} → {π} → {σ} → [Fintype σ] → LubinTateSeries F π → {H : MvPowerSeries σ O} → {L : σ → O} → HasLinearTerm H L → Prop`;
- `map_subst_inVariablesStatement : {K} → [Field K] → {F} → {π} → {σ} → [Finite σ] → LubinTateSeries F π → MvPowerSeries σ O → Prop`;
- `map_defect_eq_zeroStatement : {K} → [Field K] → {F} → {π} → {σ} → [Fintype σ] → LubinTateSeries F π → LubinTateSeries F π → {H} → {L} → HasLinearTerm H L → Prop`;
- `uniformizer_dvd_coeff_defectStatement : {K} → [Field K] → {F} → {π} → {σ} → [Fintype σ] → F.toCompleteDVF.valuation.IsUniformizer ↑π → LubinTateSeries F π → LubinTateSeries F π → {H} → {L} → HasLinearTerm H L → (σ →₀ ℕ) → Prop`.

The universes of `K`, of the value group of `F`, and of `σ` are independent,
as in the source. For every target, the `lean_check` inspection reports
`statement_returns_prop: true`, level parameters `u, v, w`, and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The element `π` is arbitrary in `O`. The only uniformizer hypothesis is the
source hypothesis `hπ` of M349.006, and no uniformizer hypothesis is added to
M349.002–M349.005. The conclusions do not mention the hypotheses `hH` and
`hπ`. They are kept as binders under the names `_hH` and `_hπ`, because the
source theorems take them and their proofs use them. The underscore only
silences the unused-variable linter. Binder names do not change a statement,
and the later proofs may use the names `hH` and `hπ`.

## Mathematical meaning

Write `O = F.valuationSubring`, `k = F.residueField` (a finite field),
`q = Nat.card k`, and `x ↦ xbar` for the residue map `F.residueMap : O → k`.
`MvPowerSeries.map F.residueMap` reduces every coefficient of a series in
`O⟦X_i : i ∈ σ⟧` to give a series in `k⟦X_i⟧`. Let
`e, ebar : LubinTateSeries F π`. These are series in `O⟦X⟧` with zero
constant coefficient and linear coefficient `π` whose reductions are
`X ^ q`. Recall that `inVariable e i = e(X_i)`, and that

`defect e ebar H = e(H) − H(ebar(X_1), ebar(X_2), …)`,

where `e(H)` is `PowerSeries.subst H e.toPowerSeries` and the second term is
`MvPowerSeries.subst (fun i ↦ inVariable ebar i) H`. A series `H` with
`HasLinearTerm H L` has `H − ∑ L_i X_i` of order at least two. In particular
`H` has zero constant coefficient.

- **M349.002**, `map_inVariableStatement e i`: the reduction of `e(X_i)` is
  `X_i ^ q` in `k⟦X_i : i ∈ σ⟧`. The variable type `σ` is arbitrary.
- **M349.003**, `map_subst_lubinTateSeriesStatement e hH`: the reduction of
  `e(H)` is `Hbar ^ q`, where `Hbar` is the reduction of `H`. The hypothesis
  `hH` provides the zero constant coefficient of `H`, so that the
  substitution is defined and commutes with reduction.
- **M349.004**, `map_subst_inVariablesStatement ebar H` (with `[Finite σ]`
  and arbitrary `H`): the reduction of `H(ebar(X_i))_i` is
  `MvPowerSeries.expand q _ Hbar`, the series `Hbar(X_i ^ q)` obtained by
  substituting `X_i ↦ X_i ^ q`. The proof argument
  `Nat.ne_of_gt Nat.card_pos : q ≠ 0` is the source's. The statement depends
  on it only through its type, by proof irrelevance.
- **M349.005**, `map_defect_eq_zeroStatement e ebar hH`: the reduction of
  `defect e ebar H` is zero. By M349.003, M349.004 and the M349.001 identity
  `Hbar(X_i ^ q) = Hbar ^ q` over the finite field `k`, both sides of the
  intertwining equation reduce to `Hbar ^ q`.
- **M349.006**, `uniformizer_dvd_coeff_defectStatement hπ e ebar hH d`:
  `π ∣ coeff d (defect e ebar H)` in `O` for every exponent `d : σ →₀ ℕ`.
  Here `hπ` says that `π`, viewed in `K`, is a uniformizer of the valuation of
  `F.toCompleteDVF`. In Mathlib this means that its valuation is the
  generator of the value group that is `< 1`. Every coefficient of the defect
  reduces to zero by M349.005, so it lies in the maximal ideal `π O`.

## Provability

The source proofs (lines 67–75, 86–92, 106–108, 116–119 and 130–133) use the
following results:

- the field `map_residue_eq_frobenius` of `LubinTateSeries`, and Mathlib's
  `PowerSeries.map_subst`, `PowerSeries.subst_pow`, `PowerSeries.subst_X`,
  `PowerSeries.HasSubst.X`, `PowerSeries.HasSubst.of_constantCoeff_zero`,
  `MvPowerSeries.map_subst`, `MvPowerSeries.expand` and
  `MvPowerSeries.substAlgHom_apply`;
- the M347 laws `HasLinearTerm.hasSubst` and
  `HasLinearTerm.constantCoeff_eq_zero` (M349.003);
- the M348.003 law `inVariable_hasSubst` (M349.004);
- M349.001 `mvPowerSeries_expand_natCard`, and M349.002–M349.004 of this module
  (M349.004 and M349.005);
- the M337.002 lemma `uniformizer_dvd_of_residueMap_eq_zero` (M349.006).

A private probe imports this module, the M349.001 target module and the
published M347 and M348 statement modules. It compiles theorems named as in
the source, each proving its target here. The prerequisites that are not yet
proved are explicit theorem arguments typed by their published statements:
`HasLinearTerm.constantCoeff_eq_zeroStatement`,
`HasLinearTerm.hasSubstStatement`, `inVariable_hasSubstStatement` and
`mvPowerSeries_expand_natCardStatement`. M337.002 is an argument with its
source type. The source proof bodies compile unchanged, apart from these
changes:

- a leading `show _ = _`, or `show _ ∣ _` for M349.006;
- explicit stand-in arguments in place of the prerequisite theorem names;
- in M349.003, the stand-in for `hH.constantCoeff_eq_zero` was first ascribed
  as `MvPowerSeries.constantCoeff H = 0` before `simp` used it. The published
  `constantCoeff_eq_zeroStatement` is a `def`, not an `abbrev`.

The source uses `simp_rw [map_inVariable]` (M349.004),
`rw [map_subst_lubinTateSeries e hH, map_subst_inVariables ebar H, …]`
(M349.005) and `congrArg (MvPowerSeries.coeff d) (map_defect_eq_zero e ebar hH)`
followed by `simpa` (M349.006). All three work verbatim with proofs of these
`abbrev` targets.

## Using the later proofs

The targets are `abbrev`s, so `rw`, `simp_rw`, `simp only`, `congrArg` and
direct term use see the underlying equation or divisibility, as checked in
the probe. A proof that starts by rewriting or simplifying its own goal
should first expose the goal with `show` or `unfold`, as the probe does. An
earlier probe for M349.001 found that `simpa` against an `abbrev` goal fails
without this step. The explicit
arguments of every target mention `σ` or a series over `σ`, so `σ` is always
inferred.

## Dependencies and modification record

The imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`,
  for `inVariable` and `defect`, and through its imports `LubinTateSeries`,
  `LocalField`, `MvPowerSeries.subst` and `PowerSeries.subst`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions`,
  for `HasLinearTerm`;
- `Mathlib.SetTheory.Cardinal.Finite`, for `Nat.card` and `Nat.card_pos`;
- `Mathlib.RingTheory.MvPowerSeries.Expand`, for `MvPowerSeries.expand`.

`Valuation.IsUniformizer` and the valuation of `F.toCompleteDVF` come
through the imports of the two definition modules.

The source imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.Intertwiner`
and `.CoefficientEquation`. They are replaced by the published definition
modules above, since the statements need only those definitions. The source
import `Mathlib.FieldTheory.Finite.Basic` is used only by source proofs, so
it is omitted.

The complete adaptations are:

1. Each of the five source theorems is replaced by a Prop-valued `abbrev`
   named `<source name>Statement`, whose binders are the source theorem's
   binders and whose body is the source conclusion verbatim. The source
   proofs are omitted.
2. The hypothesis binders `hH` (M349.003, M349.005, M349.006) and `hπ`
   (M349.006) are renamed `_hH` and `_hπ`, because the conclusions do not
   mention them.
3. The namespaces `LubinTate` and `SameUniformizer` get the prefix
   `Langlands.NYLL`.
4. The source definitions are imported from the published definition modules
   and not repeated, and the imports are changed as described above.
5. M349.001 is not part of this module (see above).
6. The source `noncomputable section` is omitted, since the module declares
   only propositions.
7. The header has a modified-file notice. There are a new module docstring
   and declaration docstrings that extend the source docstrings with the
   targeted source unit.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
NOTICE has no entry specific to this source file. The supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
