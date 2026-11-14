# NYLL M351.002–M351.004: finite-degree continuity of intertwining defects

This module states, as Prop-valued targets, exactly three theorems of the
source module `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`:
the two source-private truncation-substitution helpers M351.002 and M351.003,
and the public theorem M351.004, which says that agreement of two proposed
intertwiners (with zero constant coefficient) in every total degree at most
`m` makes the coefficients of their intertwining defects agree in every total
degree at most `m`. Nothing is proved here; each target is to be proved later
as a theorem of the same name without the `Statement` suffix:
`Langlands.NYLL.PortInternal.M351.d002`, `Langlands.NYLL.PortInternal.M351.d003`
and `Langlands.NYLL.LubinTate.SameUniformizer.coeff_defect_eq_of_coeff_eq_degree_le`.

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

Source names are in the namespace `LubinTate.SameUniformizer`.

| Source unit | Original theorem and lines | Adapted target (Lean lines) |
| --- | --- | --- |
| M351.002 | private `truncTotal_powerSeries_subst_eq_of_truncTotal_eq`, 72–80 | `Langlands.NYLL.PortInternal.M351.d002Statement` (59–71) |
| M351.003 | private `truncTotal_inVariables_subst_eq_of_truncTotal_eq`, 109–115 | `Langlands.NYLL.PortInternal.M351.d003Statement` (73–83) |
| M351.004 | `coeff_defect_eq_of_coeff_eq_degree_le`, docstring 135–142, statement 143–153 | `Langlands.NYLL.LubinTate.SameUniformizer.coeff_defect_eq_of_coeff_eq_degree_leStatement` (96–111) |

The two source-private theorems are renamed by the project rule for private
source declarations (`Langlands.NYLL.PortInternal.M351.d002Statement` and
`d003Statement`, with later proofs `…M351.d002` and `…M351.d003`); the public
theorem keeps its source name under the `Langlands.NYLL` prefix.

### Section context

The source section context of lines 33–38 and 68–70 is retained in both
namespaces of this module: universes `u v w`, the opened namespace
`LocalFieldTheory.DiscreteValuationField`, and the section variables

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}
```

The source's fourth section variable `[Fintype σ]` (line 70) is not declared,
because each of the three source theorems is preceded by
`omit [Fintype σ] in` (lines 72, 109, 135) and instead takes its own
`[Finite σ]` binder directly after the section variables. No `Fintype`,
`DecidableEq` or `HasLinearTerm` hypothesis appears in any target, as in the
source.

Inside `Langlands.NYLL.PortInternal.M351` the opens are written with full
names (`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`,
`Langlands.NYLL.LubinTate`, `Langlands.NYLL.LubinTate.SameUniformizer`), so
that, exactly as in the source namespace, `LocalField` is the shared published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`LubinTateSeries F π` is the published `Langlands.NYLL.LubinTate.LubinTateSeries F π`,
and `inVariable` and `defect` are the published M348.001 and M348.005
definitions `Langlands.NYLL.LubinTate.SameUniformizer.inVariable` and
`Langlands.NYLL.LubinTate.SameUniformizer.defect`.

### Telescopes

Each target has the complete binder list of its source theorem, in source
order: the section variables `{K} [Field K] {F} {π} {σ}`, then the source's
own binders. A private `#check` probe shows

- `d002Statement : {K : Type u} → [Field K] → {F : LocalField K} → {π : F.valuationSubring} → {σ : Type w} → [Finite σ] → LubinTateSeries F π → {H H' : MvPowerSeries σ F.valuationSubring} → constantCoeff H = 0 → constantCoeff H' = 0 → {k : ℕ} → truncTotal k H = truncTotal k H' → Prop`;
- `d003Statement : {K} → [Field K] → {F} → {π} → {σ} → [Finite σ] → LubinTateSeries F π → {H H'} → {k : ℕ} → truncTotal k H = truncTotal k H' → Prop`;
- `coeff_defect_eq_of_coeff_eq_degree_leStatement : {K} → [Field K] → {F} → {π} → {σ} → [Finite σ] → LubinTateSeries F π → LubinTateSeries F π → {H H'} → constantCoeff H = 0 → constantCoeff H' = 0 → {m : ℕ} → (∀ q : σ →₀ ℕ, q.degree ≤ m → coeff q H = coeff q H') → {d : σ →₀ ℕ} → d.degree ≤ m → Prop`,

and the development check reports the universe parameters `u`, `v`, `w`:
the universes of `K`, of the value group of `F` and of `σ` are independent.
The element `π` is arbitrary in `F.valuationSubring`; no uniformizer
hypothesis is added. The named hypotheses (`hH`, `hH'`, `htrunc`, `hcoeff`,
`hd`) are binders of the targets although the bodies do not mention them,
exactly as the source theorems take them as arguments; the unused-variables
linter is switched off for these three declarations only.

## Mathematical meaning

Write `O = F.valuationSubring`, let `e, ebar : LubinTateSeries F π` (series in
`O⟦X⟧` with zero constant coefficient and linear coefficient `π`), let `σ` be
a finite type of variables and `H, H' : MvPowerSeries σ O`. For `n : ℕ`,
`truncTotal n` (Mathlib, `Mathlib.RingTheory.MvPowerSeries.Trunc`) is the
polynomial of the monomials of total degree `< n`. Recall that
`inVariable ebar i = PowerSeries.subst (MvPowerSeries.X i) ebar.toPowerSeries`
is `ebar(X_i)` and
`defect e ebar H = PowerSeries.subst H e.toPowerSeries - MvPowerSeries.subst (fun i ↦ inVariable ebar i) H`
is `e(H) - H(ebar(X_i))_i`.

- **M351.002**, `d002Statement e hH hH' htrunc`: given
  `hH : constantCoeff H = 0`, `hH' : constantCoeff H' = 0` and
  `htrunc : H.truncTotal k = H'.truncTotal k`, the proposition
  `(PowerSeries.subst H e.toPowerSeries).truncTotal k = (PowerSeries.subst H' e.toPowerSeries).truncTotal k`:
  the composites `e(H)` and `e(H')` agree below total degree `k`.
- **M351.003**, `d003Statement ebar htrunc`: given
  `htrunc : H.truncTotal k = H'.truncTotal k`, the proposition
  `(MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k`:
  `H(ebar(X_i))_i` and `H'(ebar(X_i))_i` agree below total degree `k`. No
  constant-coefficient hypothesis on `H`, `H'` is taken, as in the source
  (each `ebar(X_i)` has zero constant coefficient).
- **M351.004**, `coeff_defect_eq_of_coeff_eq_degree_leStatement e ebar hH hH' hcoeff hd`:
  given zero constant coefficients `hH`, `hH'`, a bound `m`,
  `hcoeff : ∀ q : σ →₀ ℕ, q.degree ≤ m → coeff q H = coeff q H'` and an
  exponent `d` with `hd : d.degree ≤ m`, the proposition
  `MvPowerSeries.coeff d (defect e ebar H) = MvPowerSeries.coeff d (defect e ebar H')`.
  Thus the defect coefficients through total degree `m` depend only on the
  coefficients of the intertwiner through total degree `m`.

The source proves M351.004 by converting `hcoeff` into equality of the
truncations at `m + 1` with M351.001
(`Langlands.NYLL.LubinTate.SameUniformizer.truncTotal_succ_eq_iff_coeff_eq_degree_leStatement`,
published separately in
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U001.Statement`)
and applying M351.002 and M351.003 to the two sides of the defect. A private
draft of exactly that proof, stated against these targets and using only
Mathlib and the published definitions (with the constant coefficient of
`ebar(X_i)` computed from `PowerSeries.constantCoeff_subst_eq_zero` instead of
the not yet proved M348.002), compiles; this checks that the targets have
the source's meaning and are provable as stated.

## Using the later proofs

The targets are `abbrev`s, so a later proof can be used by term application
exactly as the source theorems are (for instance
`PortInternal.M351.d002 e hH hH' htrunc` at an expected truncation equality,
as the source's line 162 uses its private theorem), and `simp only` sees the
underlying equation. Because the hypotheses `hH`, `hH'`, `htrunc`, `hcoeff`
and `hd` are binders of the targets, a theorem stating a target passes them,
e.g.
`theorem d002 … : d002Statement e hH hH' htrunc` and
`theorem coeff_defect_eq_of_coeff_eq_degree_le … : coeff_defect_eq_of_coeff_eq_degree_leStatement e ebar hH hH' hcoeff hd`.
A private probe confirmed that `rw [d002 e hH hH' htrunc]` rewrites
directly with the equation of the target, as does `rw` after ascribing the
equation with `show`.

## Dependencies and modification record

The imports are the published M348 definition module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`
(providing `inVariable` and `defect` and, through its imports,
`LubinTateSeries`, `LocalField`, `PowerSeries.subst` and
`MvPowerSeries.subst`) and Mathlib's
`Mathlib.RingTheory.MvPowerSeries.Trunc` (providing `truncTotal`). The source
module imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`,
but none of the three statements refers to any NYLL declaration other than
`LocalField`, `LubinTateSeries`, `inVariable` and `defect`; the focused check
of this module with these two imports succeeds with no errors or warnings.

The complete adaptations are:

1. each of the three source theorems is replaced by a Prop-valued `abbrev`
   named `<adapted name>Statement`, whose binders are the source theorem's
   binders (section variables used by the theorem, then its own binders) and
   whose body is its conclusion verbatim; the source proofs (lines 81–107,
   116–133, 154–194) are omitted;
2. the source-private theorems M351.002 and M351.003 are placed in
   `Langlands.NYLL.PortInternal.M351` as `d002Statement` and `d003Statement`,
   with the source section context restated there and the opens written with
   full names; the public theorem M351.004 is in
   `Langlands.NYLL.LubinTate.SameUniformizer`;
3. the `Langlands.NYLL` prefix on the namespaces `LubinTate` and
   `SameUniformizer`;
4. the imports are reduced to the published M348 definition module and
   `Mathlib.RingTheory.MvPowerSeries.Trunc`;
5. the source `noncomputable section` and `open scoped BigOperators` are
   omitted (the module declares only propositions and uses no big
   operators), and the section instance `[Fintype σ]`, omitted by the source
   for all three theorems, is not declared; the source's
   `attribute [local instance] Classical.propDecidable` is kept (it is local;
   no decidability instance occurs in these statements);
6. `set_option linter.unusedVariables false in` on each target, because the
   named hypothesis binders are not used in the proposition bodies;
7. a modified-file notice in the header, a new module docstring and new
   declaration docstrings naming the targeted source units.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
