# NYLL M351.017 and M351.018: a monomial substituted into Lubin–Tate variables and into their linear model

This module contains the exact Prop-valued targets of two source-private
theorems of `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`:

| Source unit | Original declaration and lines | Adapted target (Lean lines) | Later exact proof name |
| --- | --- | --- | --- |
| M351.017 | `private theorem LubinTate.SameUniformizer.degree_add_one_le_order_subst_monomial_sub_linear_stabilization`, 482–527 (statement 482–490) | `Langlands.NYLL.PortInternal.M351.d017Statement` (49–62) | `Langlands.NYLL.PortInternal.M351.d017` |
| M351.018 | `private theorem LubinTate.SameUniformizer.coeff_subst_linearInVariableStabilization_monomial`, 530–553 (statement 530–536) | `Langlands.NYLL.PortInternal.M351.d018Statement` (64–74) | `Langlands.NYLL.PortInternal.M351.d018` |

Source line 481 (resp. 529) is the `omit [Fintype σ] in` line that precedes
the theorem header at 482 (resp. 530). The source proofs are omitted; each
target is to be proved by a separate exact `lean.proof@1` successor under the
listed name, with type `∀ … [Finite σ] (ebar …) d c, d017Statement ebar d c`
(resp. `∀ … {π} {σ} q d c, d018Statement (π := π) q d c`), which unfolds to
the source theorem type.

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

Both theorems are preceded by `omit [Fintype σ] in`; M351.017 adds its own
`[Finite σ]` binder and M351.018 has no finiteness hypothesis at all. The
targets therefore declare the section variables without `[Fintype σ]`:

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}
```

The resulting binder lists are those of the source theorems:

- M351.017: `{K : Type u} [Field K] {F : LocalField.{u, v} K}
  {π : F.valuationSubring} {σ : Type w} [Finite σ]
  (ebar : LubinTateSeries F π) (d : σ →₀ ℕ) (c : F.valuationSubring)`;
- M351.018: `{K : Type u} [Field K] {F : LocalField.{u, v} K}
  {π : F.valuationSubring} {σ : Type w} (q d : σ →₀ ℕ)
  (c : F.valuationSubring)`.

In M351.018 the coefficient `π` is an implicit section variable that no
explicit argument determines, exactly as in the source; a use names it, e.g.
`d018Statement (π := π) q d c`, while the source proof of M351.019 (line 585)
lets unification find it by rewriting. The universes `u`, `v`, `w` are
independent, as in the source. No uniformizer hypothesis on `π` is added: `π`
is an arbitrary element of the valuation subring (the prescribed linear
coefficient of `ebar` in M351.017).

Both targets are reducible `abbrev`s, as for the companion targets
M351.019/.020 in `MonomialSubst/InVariableStatements` and the published M348
Intertwiner targets. The source uses M351.017 as a term (`have horder := …`,
line 564) and M351.018 as a rewriting equation (`rw`, line 585), both in the
proof of M351.019. A proof `d018 … : d018Statement …` rewrites with `rw` in a
goal written out as the source equation; a goal that is itself stated as an
`abbrev` target must first be unfolded.

The local classical decidability instance of source line 31 is reproduced.
For `if q = d then … else 0` in M351.018 it supplies `DecidableEq σ`, so the
condition is decided by Mathlib's `Finsupp.instDecidableEq`, as in the
source. A focused check confirmed by `with_reducible rfl` that the condition
is `@Finsupp.instDecidableEq σ ℕ _ (classical) instDecidableEqNat q d`, and
that `rw [h]` with `h : d018Statement (π := π) q d c` rewrites the
written-out coefficient.

## Mathematical meaning

Write `O = F.valuationSubring`. Let `π ∈ O`, let `ebar : LubinTateSeries F π`,
so that `ebar.toPowerSeries ∈ O⟦X⟧` has zero constant coefficient and linear
coefficient `π`, and let `inVariable ebar i = ebar(X_i)` be the published
insertion of `ebar` into the variable `X_i`. The published M351.011 port
`d011 π i = C π * X_i` is the linear model `π X_i` of `ebar(X_i)`. For
`d : σ →₀ ℕ` write `|d| = d.degree = ∑ d_i` for the total degree.

- **M351.017.** For a finite variable type `σ`, an exponent `d` and a scalar
  `c ∈ O`, the difference
  `subst (fun i ↦ ebar(X_i)) (c X^d) - subst (d011 π) (c X^d)`, i.e.
  `c ∏_i ebar(X_i)^(d_i) - c ∏_i (π X_i)^(d_i)`, has order (lowest total
  degree of a nonzero coefficient, `MvPowerSeries.order`, valued in `ℕ∞`)
  at least `|d| + 1`. Since `ebar(X_i) - π X_i` has order at least two,
  replacing each factor by its linear model changes the product only in
  total degree above `|d|`.
- **M351.018.** For an arbitrary variable type `σ` (no finiteness
  assumption), exponents `q, d` and `c ∈ O`, the coefficient of `X^q` in
  `subst (d011 π) (c X^d) = c ∏_i (π X_i)^(d_i) = π^|d| c X^d` is
  `π^|d| · c` if `q = d` and `0` otherwise.

Both targets use Mathlib's total operation `MvPowerSeries.subst`,
`MvPowerSeries.monomial`, `MvPowerSeries.coeff`, `MvPowerSeries.order` and
`Finsupp.degree`, exactly as in the source. The exponents and the scalar are
arbitrary; `c = 0` and `d = 0` are allowed (for `c = 0` both sides of
M351.017 involve the zero series, whose order is `⊤`).

## Dependencies and modification record

The imports are

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Definitions`,
  supplying the published M351.011 port `Langlands.NYLL.PortInternal.M351.d011`
  of the source-private `linearInVariableStabilization` (same body
  `MvPowerSeries.C π * MvPowerSeries.X i` and the same explicit arguments
  `(π) (i)`, with `σ` implicit);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`,
  supplying the published M348.001
  `Langlands.NYLL.LubinTate.SameUniformizer.inVariable` and, transitively,
  `Langlands.NYLL.LubinTate.LubinTateSeries`, the shared
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField` and
  Mathlib's `MvPowerSeries.subst`;
- `Mathlib.RingTheory.MvPowerSeries.Order`, for `MvPowerSeries.order`.

The source module instead imports the whole of
`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` and
`Mathlib.RingTheory.MvPowerSeries.Trunc`; the targets need only the
declarations listed above. A focused `lean_check` of this module with these
imports succeeded, and `#check` reported the binder lists stated above.

The complete adaptations are:

1. the two theorems become Prop-valued `abbrev`s named
   `Langlands.NYLL.PortInternal.M351.d017Statement` and `d018Statement`, in
   the namespace `Langlands.NYLL.PortInternal.M351` prescribed for source
   private declarations, with the source conclusions as bodies and the source
   proofs omitted;
2. the source-private `linearInVariableStabilization (σ := σ) π` is written
   `d011 (σ := σ) π`, its published port;
3. instead of `namespace LubinTate.SameUniformizer` with
   `open LocalFieldTheory.DiscreteValuationField`, the module opens the fully
   qualified namespaces
   `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`,
   `Langlands.NYLL.LubinTate` and `Langlands.NYLL.LubinTate.SameUniformizer`,
   so that `LocalField`, `LubinTateSeries` and `inVariable` resolve to the
   published shared declarations;
4. the section variable `[Fintype σ]`, omitted by both source theorems, is not
   declared;
5. source line 30 `open scoped BigOperators` is not reproduced, since
   neither target uses big-operator notation;
6. the import replacement described above, a modified-file notice in the
   header and a module docstring.

The universes, section variables, the `[Finite σ]` binder of M351.017, the
explicit parameters, their order and types, the local classical instance and
the conclusions are otherwise unchanged. This source module has no patch10
edits.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the NOTICE
has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
