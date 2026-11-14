# NYLL M351.001: total-degree truncation through degree `m`

This module states, as a Prop-valued target, exactly the first theorem of the
source module `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`:
two multivariable power series over a finite variable type have the same
total-degree truncation `truncTotal (m + 1)` if and only if their coefficients
agree in every total degree at most `m`. Nothing is proved here; the target is
to be proved later as the theorem
`Langlands.NYLL.LubinTate.SameUniformizer.truncTotal_succ_eq_iff_coeff_eq_degree_le`.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The source-file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence

| Source unit | Original theorem and lines | Adapted target (Lean lines) |
| --- | --- | --- |
| M351.001 | `LubinTate.SameUniformizer.truncTotal_succ_eq_iff_coeff_eq_degree_le`, docstring 40–41, statement 42–48 | `Langlands.NYLL.LubinTate.SameUniformizer.truncTotal_succ_eq_iff_coeff_eq_degree_leStatement` (36–45) |

The source theorem stands before the source's `variable` commands (lines
68–70), so it has no section variables. Its binders are reproduced exactly and
in order:

```lean
{R : Type*} [CommSemiring R]
{τ : Type*} [Finite τ]
{H H' : MvPowerSeries τ R} (m : ℕ)
```

so the target has the telescope
`{R : Type u_1} → [CommSemiring R] → {τ : Type u_2} → [Finite τ] → {H H' : MvPowerSeries τ R} → ℕ → Prop`
with two independent universe parameters (the development check reports level
parameters `u_1`, `u_2`). The ring is an arbitrary commutative semiring and
the variable type an arbitrary `Finite` type: no `CommRing`, `Fintype` or
`DecidableEq` assumption is added. The body is the source conclusion
verbatim:

```lean
H.truncTotal (m + 1) = H'.truncTotal (m + 1) ↔
  ∀ d : τ →₀ ℕ, d.degree ≤ m →
    MvPowerSeries.coeff d H = MvPowerSeries.coeff d H'
```

## Mathematical meaning

`MvPowerSeries.truncTotal n` (Mathlib, `Mathlib.RingTheory.MvPowerSeries.Trunc`,
requiring `[Finite τ]`) is the `R`-linear map sending a power series to the
polynomial formed by its monomials of total degree `< n`; `d.degree` is the
total degree `∑ i, d i` of an exponent `d : τ →₀ ℕ`. The target says: for
power series `H`, `H'` in variables `τ` over `R` and `m : ℕ`, the polynomials
of the monomials of total degree `≤ m` of `H` and of `H'` coincide if and only
if `coeff d H = coeff d H'` for every exponent `d` of total degree `≤ m`.

## Using the later proof

The target is an `abbrev`, so `.1`/`.2`, `.mp`/`.mpr` and `simp only` on a
proof see the underlying `↔`; the source's own later use
`(truncTotal_succ_eq_iff_coeff_eq_degree_le (H := H) (H' := H') m).2 hcoeff`
(source line 157) works unchanged, as a private probe confirmed. `rw` with the
proof does not rewrite, because `rw` does not unfold the target to its `↔`;
use `simp only`, `.mp`/`.mpr`, or ascribe the proposition with `show` first.
The series `H`, `H'` remain implicit as in the source, so a theorem stating
the target writes
`truncTotal_succ_eq_iff_coeff_eq_degree_leStatement (H := H) (H' := H') m`.

## Dependencies and modification record

The only import is Mathlib's `Mathlib.RingTheory.MvPowerSeries.Trunc`, which
provides `MvPowerSeries.truncTotal`, `MvPowerSeries.coeff` and
`Finsupp.degree`. The source module imports
`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` as well,
but the statement uses no NYLL declaration; the focused check of this module
with the Mathlib import alone succeeds.

The complete adaptations are:

1. the source theorem is replaced by a Prop-valued `abbrev` named
   `truncTotal_succ_eq_iff_coeff_eq_degree_leStatement`, whose binders are the
   source theorem's binders and whose body is its conclusion verbatim; the
   source proof (lines 49–66) is omitted;
2. the `Langlands.NYLL` prefix on the namespaces `LubinTate` and
   `SameUniformizer`;
3. the imports are reduced to `Mathlib.RingTheory.MvPowerSeries.Trunc`;
4. the source `noncomputable section`, `open scoped BigOperators`,
   `universe u v w`, `open LocalFieldTheory.DiscreteValuationField` and the
   section variables of lines 68–70 are omitted, since the source theorem
   uses none of them; the source's `attribute [local instance]
   Classical.propDecidable` is kept (it is local and does not affect this
   statement, which elaborates no decidability instance);
5. a modified-file notice in the header, a new module docstring and a new
   declaration docstring naming the targeted source unit.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
