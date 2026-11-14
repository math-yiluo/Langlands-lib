# NYLL M351.019 and M351.020: low-degree coefficients of a monomial substituted into Lubin–Tate variables

This module contains the exact Prop-valued targets of two source-private
theorems of `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`:

| Source unit | Original declaration and lines | Adapted target (Lean lines) | Later exact proof name |
| --- | --- | --- | --- |
| M351.019 | `private theorem LubinTate.SameUniformizer.coeff_subst_inVariables_monomial_of_degree_le`, 556–585 (statement 556–563) | `Langlands.NYLL.PortInternal.M351.d019Statement` (47–58) | `Langlands.NYLL.PortInternal.M351.d019` |
| M351.020 | `private theorem LubinTate.SameUniformizer.coeff_subst_inVariables_add_monomial_of_degree_le`, 588–602 (statement 588–598) | `Langlands.NYLL.PortInternal.M351.d020Statement` (60–75) | `Langlands.NYLL.PortInternal.M351.d020` |

Source line 555 (resp. 587) is the `omit [Fintype σ] in` line that precedes
the theorem header at 556 (resp. 588). The source proofs are omitted; each
target is to be proved by a separate exact `lean.proof@1` successor under the
listed name, with type
`∀ … [Finite σ] (ebar …) …, d019Statement ebar q d hq c` (and similarly for
`d020Statement ebar H q d hq c`), which unfolds to the source theorem type.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, with
source-file SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717` (checked
against the readable snapshot at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`).
The registered sources are `external-lean-reuse-snapshots-2026-10-21` and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`. No
applicable NYLL entry exists in `notes/errata/`.

## Source context retained

The relevant source context is:

- line 28 `noncomputable section`, line 31
  `attribute [local instance] Classical.propDecidable`, line 33
  `universe u v w`, lines 35–36 `namespace LubinTate` /
  `namespace SameUniformizer`, line 38
  `open LocalFieldTheory.DiscreteValuationField`;
- the section variables of lines 68–70:

  ```lean
  variable {K : Type u} [Field K]
  variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
  variable {σ : Type w} [Fintype σ]
  ```

Both theorems are preceded by `omit [Fintype σ] in` and add their own
`[Finite σ]` binder. The targets therefore declare the section variables
without `[Fintype σ]` and keep `[Finite σ]` as the first own binder:

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

abbrev d019Statement [Finite σ]
    (ebar : LubinTateSeries F π)
    (q d : σ →₀ ℕ) (_hq : q.degree ≤ d.degree)
    (c : F.valuationSubring) : Prop := …
```

The resulting binder list of each target is that of its source theorem:
`{K : Type u} [Field K] {F : LocalField.{u, v} K} {π : F.valuationSubring}
{σ : Type w} [Finite σ] (ebar : LubinTateSeries F π)`, then for M351.020 the
explicit `(H : MvPowerSeries σ F.valuationSubring)`, then
`(q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree) (c : F.valuationSubring)`. The
universes `u`, `v`, `w` of the field, of the value group of the local field
and of the variable type are independent, as in the source. No uniformizer
hypothesis on `π` is added: `π` is the arbitrary prescribed linear coefficient
of `ebar`. The hypothesis `hq` is named `_hq` because a proposition body does
not use it; it remains an explicit binder so that the target has the full
source signature.

Both targets are reducible `abbrev`s, as for the published M348
Intertwiner targets of the same route. The source uses each theorem as a
rewriting equation (M351.019 by `rw` at source line 602 in the proof of
M351.020, and M351.020 by `simp only` at line 792 in the later
coefficient-response unit M351.025); with reducible targets the exact
proofs `d019 … : d019Statement …` and `d020 … : d020Statement …` can be used
by `rw` and `simp only` in the same way. A focused check confirmed this: in
a goal written out as the source equation, `rw [h]` with
`h : d019Statement ebar q d hq c` and `simp only [h]` with
`h : d020Statement ebar H q d hq c` both rewrite. A goal that is itself
stated as `d020Statement …` must first be unfolded (for example by
`unfold`) before its inner terms can be rewritten.

The local classical decidability instance of source line 31 is reproduced.
It determines the decidability instance of `if q = d then … else 0`: a
focused check showed that the elaborated condition uses Mathlib's
`Finsupp.instDecidableEq` at `q d`, with `DecidableEq σ` supplied by
`Classical.propDecidable` and `DecidableEq ℕ` by `instDecidableEqNat`, not
`Classical.propDecidable (q = d)` directly. The same instances are available
in the source's import closure, so this is the source elaboration.

## Mathematical meaning

Write `O = F.valuationSubring`, let `ebar : LubinTateSeries F π`, so that
`ebar.toPowerSeries ∈ O⟦X⟧` has zero constant coefficient and linear
coefficient `π`, and let `inVariable ebar i = ebar(X_i)` be the published
insertion of `ebar` into the variable `X_i`. For `d : σ →₀ ℕ` write
`|d| = d.degree = ∑ d_i` for the total degree.

- **M351.019.** For a finite variable type `σ`, exponents `q, d` with
  `|q| ≤ |d|` and a scalar `c ∈ O`, the coefficient of `X^q` in
  `MvPowerSeries.subst (fun i ↦ ebar(X_i)) (c X^d)`, i.e. in
  `c ∏_i ebar(X_i)^(d_i)`, equals `π^|d| · c` if `q = d` and `0` otherwise.
  Each `ebar(X_i) = π X_i + (terms of degree ≥ 2)`, so up to total degree
  `|d|` the substituted monomial agrees with `π^|d| c X^d`.
- **M351.020.** For a finite `σ`, an arbitrary `H ∈ O⟦X_σ⟧` and the same
  data, the coefficient of `X^q` in the substitution of `H + c X^d` equals
  the coefficient of `X^q` in the substitution of `H` plus
  `if q = d then π^|d| · c else 0`. No hypothesis on `H` (zero constant
  coefficient, prescribed linear term, or anything else) is imposed; the
  substitution `fun i ↦ ebar(X_i)` is admissible because each `ebar(X_i)`
  has zero constant coefficient and `σ` is finite, which is what makes
  substitution additive.

Both targets use Mathlib's total operation `MvPowerSeries.subst`, the
coefficient map `MvPowerSeries.coeff`, `MvPowerSeries.monomial` and
`Finsupp.degree`, exactly as in the source. The scalar `c` and the exponents
`q`, `d` are arbitrary; `c = 0` and `d = 0` are allowed (for `d = 0` only
`q = 0` satisfies `|q| ≤ |d|`, and the coefficient is `c = π^0 c`).

## Dependencies and modification record

The single import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`,
which supplies the published M348.001
`Langlands.NYLL.LubinTate.SameUniformizer.inVariable` and, transitively, the
published M336.001 `Langlands.NYLL.LubinTate.LubinTateSeries`, the shared
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField` and
Mathlib's `Mathlib.RingTheory.MvPowerSeries.Substitution`. The source module
instead imports the whole of
`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` and
`Mathlib.RingTheory.MvPowerSeries.Trunc`; neither target mentions recursive
correction coefficients (M350), truncation, orders or the private linear model
`linearInVariableStabilization` (M351.011), so those imports are not needed.
A focused `lean_check` of this module with only this import succeeded, and
inspection reported `statement_returns_prop: true` for both targets.

The complete adaptations are:

1. the two theorems become Prop-valued `abbrev`s named
   `Langlands.NYLL.PortInternal.M351.d019Statement` and `d020Statement`, in
   the namespace `Langlands.NYLL.PortInternal.M351` prescribed for source
   private declarations, with the source conclusions as bodies and the source
   proofs omitted;
2. instead of `namespace LubinTate.SameUniformizer` with
   `open LocalFieldTheory.DiscreteValuationField`, the module opens the
   fully qualified namespaces
   `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`,
   `Langlands.NYLL.LubinTate` and `Langlands.NYLL.LubinTate.SameUniformizer`,
   so that `LocalField`, `LubinTateSeries` and `inVariable` resolve to the
   published shared declarations;
3. the section variable `[Fintype σ]`, omitted by both source theorems, is not
   declared;
4. the hypothesis `hq` is renamed `_hq`;
5. source line 30 `open scoped BigOperators` is not reproduced, since
   neither target uses big-operator notation;
6. the import replacement described above, a modified-file notice in the
   header and a module docstring.

The universes, section variables, `[Finite σ]` binders, explicit parameters,
their order and types, the local classical instance and the conclusions are
otherwise unchanged. This source module has no patch10 edits.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the NOTICE
has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
