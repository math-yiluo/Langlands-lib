# NYLL M351.016: agreement with the linear model below degree two

The theorem `Langlands.NYLL.PortInternal.M351.d016` proves the published
target `Langlands.NYLL.PortInternal.M351.d016Statement`:

```lean
theorem d016 (ebar : LubinTateSeries F π) (i : σ) :
    d016Statement ebar i
```

Here `{K : Type u} [Field K]`, `{F : LocalField.{u, v} K}`,
`{π : F.valuationSubring}` and `{σ : Type w}` are implicit parameters,
in that order. There is no finiteness assumption on `σ`.
The target unfolds to
`(2 : ℕ∞) ≤ (inVariable ebar i - d011 π i).order`.
Thus the inserted series `ebar(X_i)` and its linear model
`d011 π i = MvPowerSeries.C π * MvPowerSeries.X i` have equal
coefficients in every total degree below two.

## Original source and correspondence

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
lines 437–479: the private theorem
`LubinTate.SameUniformizer.two_le_order_inVariable_sub_linearInVariableStabilization`.
This is unit M351.016, adapted here under its required public name `d016`.
The source file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.

The readable original is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL entry was found in `notes/errata/`.

## Implemented proof

The proof follows the original coefficient argument. After exposing the
target's underlying proposition, `MvPowerSeries.nat_le_order` reduces it
to the vanishing of each coefficient of the difference at an exponent
`d : σ →₀ ℕ` with `d.degree < 2`. The coefficient map preserves subtraction.
The proof splits on whether `d = Finsupp.single i (d i)`.

1. If this equality holds and `d i = 0`, then `d = 0`. Substitution into
   `X_i` has the constant coefficient of `ebar`, which is zero by
   `LubinTateSeries.constantCoeff_eq_zero`; the linear model also has
   zero constant coefficient.
2. If the equality holds and `d i ≠ 0`, then
   `Finsupp.degree_single` identifies `d.degree` with `d i`. The bound
   `d.degree < 2` and `omega` give `d i = 1`, hence
   `d = Finsupp.single i 1`. Both coefficients equal `π`, using
   `LubinTateSeries.coeff_one_eq_uniformizer`.
3. Otherwise, `PowerSeries.coeff_subst_single` makes the coefficient of
   `ebar(X_i)` zero. The exponent is also different from
   `Finsupp.single i 1`, so `MvPowerSeries.coeff_X` makes the coefficient
   of the linear model zero.

Each case closes by simplification after unfolding `inVariable` and `d011`.
The proof uses only the two stated coefficient fields of `LubinTateSeries`;
its residue-Frobenius field is not needed.

## Dependencies and modifications

The only direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements`.
Its published imports supply `d011`, `inVariable`, `LubinTateSeries`,
`LocalField`, and Mathlib's multivariable order and power-series substitution
results. No other M351 proof is used.

Worker 560 made these modifications on 16 November 2026:

- extract the single private source theorem, remove `private`, and rename it
  to `Langlands.NYLL.PortInternal.M351.d016`;
- state its result using the existing reducible `d016Statement` and add the
  initial `show` of its underlying proposition;
- replace the source-private `linearInVariableStabilization` with its
  published definition name `d011`, and qualify the opened NYLL namespaces;
- replace the original RecursiveCoefficient and MvPowerSeries.Trunc imports
  with the focused published statement module;
- omit the unused section `Fintype σ` instance and its corresponding `omit`
  command, the noncomputable section, the BigOperators opening and the local
  `Classical.propDecidable` instance; retain the proof's own `classical`;
- add the modification notice, module documentation and theorem docstring.

The source proof after the initial `show` is unchanged apart from the
definition's name. The elaborated source binders and conclusion are
preserved. Published statement, definition and imported files are unchanged.

## License

The original copyright, Apache-2.0 release line and author header are
preserved verbatim. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
