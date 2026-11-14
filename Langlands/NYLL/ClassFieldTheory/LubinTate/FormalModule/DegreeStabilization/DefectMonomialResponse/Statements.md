# NYLL M351.024, M351.025 and M351.026: response of the intertwining defect to one monomial

This module states three theorems of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization` as
Prop-valued targets. Two are source-private (M351.024 and M351.025) and one is
public (M351.026). Together they say what happens when one monomial `c X^d` is
added to a series `H`. In total degrees up to `d.degree`, the coefficients of
`e(H)` and of the intertwining defect of `H` move only in the coordinate `d`,
and by an explicit scalar. This module proves nothing. Each target is to be
proved later by a theorem with the same name minus the `Statement` suffix.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The source file's SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
A readable copy is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
`notes/errata/` has no NYLL entry that applies. The source units and planned
names come from the port inventory `notes/reuse/nyll-public-port/m337-m360.md`
(section M351, rows M351.024–M351.026).

## Source correspondence

| Source unit | Original theorem and source lines | Adapted target (Lean lines) |
| --- | --- | --- |
| M351.024 | `LubinTate.SameUniformizer.coeff_subst_lubinTateSeries_add_monomial_of_degree_le`, `private`. `omit [Fintype σ] in` at 698, signature 699–711, proof to 772 | `Langlands.NYLL.PortInternal.M351.d024Statement` (54–71) |
| M351.025 | `LubinTate.SameUniformizer.coeff_defect_add_monomial_eq_of_degree_le_constantCoeff`, `private`. `omit [Fintype σ] in` at 774, signature 775–786, proof to 809 | `Langlands.NYLL.PortInternal.M351.d025Statement` (73–90) |
| M351.026 | `LubinTate.SameUniformizer.coeff_defect_add_monomial_eq_of_degree_le`, public. Docstring 811–813, signature 814–825, proof 826–827 | `Langlands.NYLL.LubinTate.SameUniformizer.coeff_defect_add_monomial_eq_of_degree_leStatement` (103–119) |

The module keeps the source context these theorems use:

- `attribute [local instance] Classical.propDecidable` (source line 31; Lean line 43);
- `universe u v w` (source line 33; Lean line 41);
- `open LocalFieldTheory.DiscreteValuationField` (source line 38). Here it is
  `open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`;
- the section variables of source lines 68–70:

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]
```

The source removes the section instance `[Fintype σ]` from M351.024 and
M351.025 with `omit [Fintype σ] in`. The Lean module therefore declares
`variable {σ : Type w}` without the instance. It writes `[Fintype σ]` as the
first explicit binder of the M351.026 target only, which is where the source
section variable sits in that theorem's telescope. M351.025's own source
binder `[Finite σ]` appears in the same position. M351.024 has no finiteness
hypothesis on `σ`.

A private `#check` probe shows these telescopes. `LocalField` is the published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`, and
`O := F.valuationSubring`.

- `d024Statement : {K : Type u} → [Field K] → {F : LocalField.{u,v} K} → {π : O} → {σ : Type w} → LubinTateSeries F π → {H : MvPowerSeries σ O} → constantCoeff H = 0 → (q d : σ →₀ ℕ) → q.degree ≤ d.degree → 1 ≤ d.degree → O → Prop`;
- `d025Statement : {K} → [Field K] → {F} → {π} → {σ} → [Finite σ] → LubinTateSeries F π → LubinTateSeries F π → {H} → constantCoeff H = 0 → (q d : σ →₀ ℕ) → q.degree ≤ d.degree → 1 ≤ d.degree → O → Prop`;
- `coeff_defect_add_monomial_eq_of_degree_leStatement : {K} → [Field K] → {F} → {π} → {σ} → [Fintype σ] → LubinTateSeries F π → LubinTateSeries F π → {H} → {L : σ → O} → HasLinearTerm H L → (q d : σ →₀ ℕ) → q.degree ≤ d.degree → 2 ≤ d.degree → O → Prop`.

These match the source theorems binder by binder: binder kinds, order and
types. The universes of `K`, of the value group of `F`, and of `σ` are
independent. The element `π` is any element of `F.valuationSubring`. None of
the three targets adds a uniformizer hypothesis. Each body is the source
theorem's conclusion, verbatim.

`LubinTateSeries F π` is the published `Langlands.NYLL.LubinTate.LubinTateSeries`.
`defect` is the published M348.005 definition in
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`.
`HasLinearTerm` is the published M347.003 definition in
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions`.
The source module uses exactly these names after its namespaces are prefixed.

## Mathematical meaning

Write `O = F.valuationSubring`. Let `e, ebar : LubinTateSeries F π` be
one-variable series over `O` with zero constant coefficient and linear
coefficient `π`, satisfying the residue-field Frobenius condition of the
structure. Let `H : MvPowerSeries σ O`, let `q d : σ →₀ ℕ` be exponents with
`q.degree ≤ d.degree`, and let `c : O`. The *defect* is
`defect e ebar H = e(H) - H(ebar(X_i))_i`, i.e.
`PowerSeries.subst H e.toPowerSeries - MvPowerSeries.subst (fun i ↦ inVariable ebar i) H`.

- **M351.024**, `d024Statement e hH q d hq hd c`: if `constantCoeff H = 0`
  and `1 ≤ d.degree`, then
  `coeff q (e(H + c X^d)) = coeff q (e(H)) + π * (if q = d then c else 0)`.
  Here `e(·)` is `PowerSeries.subst · e.toPowerSeries`. In total degrees up to
  `d.degree`, only the linear term of `e` sees the new monomial, so the
  coefficient of `X^q` changes by `π c` exactly when `q = d`. `σ` may be
  infinite.
- **M351.025**, `d025Statement e ebar hH q d hq hd c` (with `[Finite σ]`):
  under the same hypotheses `constantCoeff H = 0` and `1 ≤ d.degree`,
  `coeff q (defect e ebar (H + c X^d)) = coeff q (defect e ebar H) +
  (if q = d then π * ((1 - π ^ (d.degree - 1)) * c) else 0)`.
  The left-hand side of the defect changes by `π c` at `X^d`, as in M351.024.
  The right-hand side `H(ebar(X_i))_i` changes, in those degrees, by
  `π^{d.degree} c` at `X^d` only. The difference is
  `π c - π^{d.degree} c = π (1 - π^{d.degree - 1}) c`.
- **M351.026**, `coeff_defect_add_monomial_eq_of_degree_leStatement e ebar hH q d hq hd c`
  (with `[Fintype σ]`): the same conclusion as M351.025, under the hypotheses
  `HasLinearTerm H L` (so `H - ∑ i, L i X_i` has total order at least two)
  and `2 ≤ d.degree`. Neither hypothesis appears in the conclusion. The
  source docstring says: adding a monomial of degree `d.degree` changes no
  defect coefficient in lower total degree, and changes the same-degree
  block only in the `d` coordinate. This is the cancellation law that the
  source's recursive correction and uniqueness arguments use.

`MvPowerSeries.monomial d c` is the series `c X^d`. `d.degree`
(`Finsupp.degree`) is the total degree of `d`, the sum of its entries over its
support. The subtraction `d.degree - 1` is natural-number
subtraction. It is the ordinary one under the `1 ≤ d.degree` and
`2 ≤ d.degree` hypotheses that every target carries.

## Decidability of `if q = d`

As in the source (line 31), the module enables `Classical.propDecidable` as a
local instance. Without it, `if q = d` does not elaborate, because `σ` has no
`DecidableEq` instance. A private probe shows how the condition elaborates:
the decision procedure is
`Finsupp.instDecidableEq σ ℕ (fun a b ↦ Classical.propDecidable (a = b)) instDecidableEqNat q d`.
This is the instance the source theorems get from the same local-instance
setting. A downstream module that enables the same local instance, as the
source module does, therefore produces a syntactically identical `if q = d`
term. Rewriting with these results then works exactly as it does in the
source.

## Using the later proofs

The targets are `abbrev`s whose bodies are equations. A later theorem
`theorem coeff_defect_add_monomial_eq_of_degree_le … : coeff_defect_add_monomial_eq_of_degree_leStatement e ebar hH q d hq hd c`
can therefore be used like the source theorem. A private probe confirmed
that `rw [h e ebar hH d d le_rfl hd c]` rewrites a goal about
`coeff d (defect e ebar (H + monomial d c))` when `h` is a proof of the
M351.026 target, and that `rw` also works with a proof of the M351.024
target. It also confirmed that `simp only [h024 e hH q d hq hd c, …]` uses
a proof of the M351.024 target inside the source proof of M351.025, and that
a proof of M351.025 closes the M351.026 target as the source term proof
does. The source proofs use these predecessor units:

- M351.024: the M351.021 constant-coefficient lemma for `monomial d c`, the
  M351.023 power expansion `coeff_pow_add_monomial_of_degree_le`, and the
  `LubinTateSeries` field `coeff_one_eq_uniformizer`;
- M351.025: M351.024 and the M351.020 substitution response
  `coeff_subst_inVariables_add_monomial_of_degree_le`;
- M351.026: M351.025 and the M347.004 result `HasLinearTerm.constantCoeff_eq_zero`.

Those predecessors belong to other tasks. This module neither imports nor
claims them.

## Dependencies and modification record

The module imports two published definition modules. The first is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`,
which provides `defect` and, through its imports, `LubinTateSeries`,
`LocalField`, `PowerSeries.subst` and `MvPowerSeries.subst`. The second is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions`,
which provides `HasLinearTerm`.

These are all the adaptations:

1. Each of the three source theorems becomes a Prop-valued `abbrev`. Its
   binders are the source theorem's binders, including the section variables
   it uses. Its body is the source conclusion, verbatim. The source proofs
   are omitted.
2. The two private theorems receive the planned names
   `Langlands.NYLL.PortInternal.M351.d024Statement` and `d025Statement`. The
   public theorem keeps its source name in
   `Langlands.NYLL.LubinTate.SameUniformizer`, with the `Statement` suffix.
3. Hypotheses that the conclusion does not mention (`hH`, `hq`, `hd`) are
   renamed with a leading underscore. Their types and binder kinds are
   unchanged.
4. The `omit [Fintype σ] in` modifiers become a section declaration without
   the instance, plus an explicit `[Fintype σ]` binder on the M351.026 target
   only, at the position where the source section variable sits.
5. The source imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`
   and `Mathlib.RingTheory.MvPowerSeries.Trunc` are replaced by the two
   published definition modules above, which supply every name the
   statements use.
6. The `Langlands.NYLL` prefix is added to the namespaces `LubinTate`,
   `SameUniformizer` and `LocalFieldTheory.DiscreteValuationField`. The two
   private targets live in `Langlands.NYLL.PortInternal.M351`, which opens
   `Langlands.NYLL.LubinTate` and `Langlands.NYLL.LubinTate.SameUniformizer`
   so that `LubinTateSeries` and `defect` resolve to the same declarations
   as in the source namespace.
7. The source `noncomputable section` and `open scoped BigOperators` are
   omitted. The module declares only propositions, and none of them uses
   big-operator notation.
8. The header gains a modified-file notice. The module docstring and the
   declaration docstrings are new and name the source units they target.

The original 2026 copyright line, Apache-2.0 release line and author header
are kept. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
NOTICE has no entry specific to this source file. The supplement's
third-party attribution table
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_ATTRIBUTION.md` does not list any
`LubinTate` file.

## Development verification

The module was compiled in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) against the published definition
modules. Exact-declaration inspections of the three targets reported
`statement_returns_prop: true` with no warnings or errors. This development
check does not establish independent semantic acceptance, and it proves none
of the targets.
