# NYLL M351.005–.010: order estimates for multivariable power series (targets)

The paired module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements`
defines six Prop-valued targets
`Langlands.NYLL.PortInternal.M351.d005Statement` through
`Langlands.NYLL.PortInternal.M351.d010Statement`. It proves none of them.
They are lower bounds for Mathlib's total order `MvPowerSeries.order` of a
monomial, of a power, of a finite sum, of a finite product of powers, of a
difference of two powers and of a difference of two finite products of powers,
over an arbitrary commutative ring and an arbitrary variable type.

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717` (checked
against the pinned copy). The
[complete pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean>)
was read, including the six proofs and the context lines cited below. The
registered sources are `external-lean-reuse-snapshots-2026-10-21` (the source
snapshot) and `nyll-classfieldtheory-fbd320cd-supplement` (attribution, notice
and CI files of the same commit).

| Unit | Original private theorem | Source signature | Source proof | Adapted target |
| --- | --- | --- | --- | --- |
| M351.005 | `LubinTate.SameUniformizer.degree_le_order_monomial_stabilization` | lines 196–199 | 200–203 | `Langlands.NYLL.PortInternal.M351.d005Statement` |
| M351.006 | `LubinTate.SameUniformizer.natCast_le_order_pow_of_one_le_order_stabilization` | lines 205–209 | 210–213 | `Langlands.NYLL.PortInternal.M351.d006Statement` |
| M351.007 | `LubinTate.SameUniformizer.le_order_finset_sum_stabilization` | lines 215–219 | 220–231 | `Langlands.NYLL.PortInternal.M351.d007Statement` |
| M351.008 | `LubinTate.SameUniformizer.natCast_sum_le_order_finset_prod_pow_stabilization` | lines 233–238 | 239–257 | `Langlands.NYLL.PortInternal.M351.d008Statement` |
| M351.009 | `LubinTate.SameUniformizer.order_sub_add_pred_le_order_pow_sub_pow_stabilization` | lines 259–266 | 267–295 | `Langlands.NYLL.PortInternal.M351.d009Statement` |
| M351.010 | `LubinTate.SameUniformizer.natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization` | lines 297–307 | 308–398 | `Langlands.NYLL.PortInternal.M351.d010Statement` |

The names follow the NYLL partition `notes/reuse/nyll-public-port/m337-m360.md`
(section M351): `M351` is this source module and `d005`–`d010` its fifth to
tenth declaration commands. They are fresh public names for source-private
theorems, not the original private kernel names.

### Source context and what is dropped

The source context is `noncomputable section` (line 28),
`open scoped BigOperators` (line 30),
`attribute [local instance] Classical.propDecidable` (line 31),
`universe u v w` (line 33), namespaces `LubinTate` and `SameUniformizer`
(lines 35–36), `open LocalFieldTheory.DiscreteValuationField` (line 38) and the
section variables `{K : Type u} [Field K]`, `{F : LocalField.{u, v} K}`,
`{π : F.valuationSubring}` and `{σ : Type w} [Fintype σ]` (lines 68–70).

None of the six signatures mentions `K`, `F`, `π` or `σ`, so Lean does not
include any of these section variables (or `[Fintype σ]`) in the six source
theorems; they are not parameters here either. Every type in the six
signatures is declared by the theorem itself with `Type*`. No signature needs
a decidability instance (`MvPowerSeries.monomial` takes none, and finite sums
and products over a given `Finset` take none), so the local
`Classical.propDecidable` instance does not enter any of the six types and is
not reproduced. The source module imports
`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` and
`Mathlib.RingTheory.MvPowerSeries.Trunc`; neither is needed by these
signatures. The only import here is `Mathlib.RingTheory.MvPowerSeries.Order`,
which supplies `MvPowerSeries.order`, `MvPowerSeries.monomial`,
`Finsupp.degree`, `ℕ∞` and the big-operator notation. The source proofs are
omitted.

### Adaptations

- Namespace `LubinTate.SameUniformizer` becomes
  `Langlands.NYLL.PortInternal.M351`, and each source-private theorem becomes a
  public target `d00kStatement`.
- Each target is an `abbrev` (a reducible definition returning `Prop`). Its
  parameters are exactly the source binders before the colon, in source order
  and with source binder kinds (implicit, instance-implicit, explicit),
  including the hypotheses; its body is the source conclusion verbatim. The
  later proof `Langlands.NYLL.PortInternal.M351.d00k` can therefore take the
  source telescope and have type `d00kStatement` applied to its binders, and is
  used exactly like the source theorem (for instance `d006 f n hf`).
  Reducibility lets consumers use the proofs in `calc` steps, `le_trans`,
  `add_le_add` and similar term positions without unfolding.
- The source writes `{R : Type*}`, `{τ : Type*}` and, where present,
  `{ι : Type*}`, giving three independent universe variables. Here they are
  named `u`, `v` and `w` respectively (fresh names, unrelated to the source's
  section universes `u v w` of `K`, `F` and `σ`); no relation among them is
  imposed. `d005Statement`, `d006Statement` and `d009Statement` have universe
  parameters `u, v`; the others have `u, v, w`.
- Hypothesis parameters are not used in the bodies; to silence the unused
  variable linter they carry an underscore prefix (`_hf`, `_hg`, `_h`, `_hn`,
  `_hfg` for the source `hf`, `hg`, `h`, `hn`, `hfg`). Binder names do not
  change the proposition.

## The targets

In all six, `R` is an arbitrary commutative ring (`[CommRing R]`, as in the
source), `τ` an arbitrary type of variables (possibly infinite or empty) and
`ι` an arbitrary index type; there are no finiteness, decidability, field or
local-field hypotheses. `MvPowerSeries.order f : ℕ∞` is Mathlib's total order:
the least total degree `Finsupp.degree d = ∑ i ∈ d.support, d i` of an exponent
`d` with nonzero coefficient, and `⊤` exactly when `f = 0`. Hence
`(1 : ℕ∞) ≤ f.order` says that `f` has zero constant coefficient.

### M351.005

```lean
abbrev d005Statement
    {R : Type u} [CommRing R] {τ : Type v}
    (d : τ →₀ ℕ) (c : R) : Prop :=
  (d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order
```

The monomial `c X^d` has order at least the total degree of `d`. The
coefficient `c` may be zero (then the monomial is `0` and its order is `⊤`).

### M351.006

```lean
abbrev d006Statement
    {R : Type u} [CommRing R] {τ : Type v}
    (f : MvPowerSeries τ R) (n : ℕ)
    (_hf : (1 : ℕ∞) ≤ f.order) : Prop :=
  (n : ℕ∞) ≤ (f ^ n).order
```

If `f` has zero constant coefficient, then `f ^ n` has order at least `n`, for
every natural `n` including `0`.

### M351.007

```lean
abbrev d007Statement
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (_h : ∀ i ∈ s, m ≤ (f i).order) : Prop :=
  m ≤ (∑ i ∈ s, f i).order
```

A bound `m ∈ ℕ∞` (possibly `⊤`) on the orders of all summands indexed by `s`
bounds the order of the finite sum. The hypothesis concerns only indices in
`s`; for empty `s` the sum is `0`. `s`, `f` and `m` are implicit, as in the
source, and are determined by the hypothesis.

### M351.008

```lean
abbrev d008Statement
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (_hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) : Prop :=
  ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤
    (∏ i ∈ s, (f i) ^ n i).order
```

If every `f i` with `i ∈ s` has zero constant coefficient, the product
`∏ i ∈ s, f i ^ n i` has order at least the natural number `∑ i ∈ s, n i`,
cast to `ℕ∞`. Exponents may be zero; `s` is implicit as in the source.

### M351.009

```lean
abbrev d009Statement
    {R : Type u} [CommRing R] {τ : Type v}
    (f g : MvPowerSeries τ R)
    (_hf : (1 : ℕ∞) ≤ f.order)
    (_hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) : Prop :=
  (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
    (f ^ n - g ^ n).order
```

For `f`, `g` with zero constant coefficient,
`ord(f ^ n - g ^ n) ≥ ord(f - g) + (n - 1)`. The subtraction `n - 1` is
truncated subtraction in `ℕ`, then cast to `ℕ∞`; for `n = 0` the right side
is the order of `0`, namely `⊤`. Addition is that of `ℕ∞`, so `f = g` gives
`⊤` on both sides. The explicit argument `n` comes after the two hypotheses,
as in the source.

### M351.010

```lean
abbrev d010Statement
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (_hn : ∀ i ∈ s, n i ≠ 0)
    (_hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (_hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (_hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) : Prop :=
  (((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤
    ((∏ i ∈ s, (f i) ^ n i) -
      ∏ i ∈ s, (g i) ^ n i).order
```

If, for every `i ∈ s`, the exponent `n i` is nonzero, `f i` and `g i` have zero
constant coefficient and `f i - g i` has order at least two, then
`∏ i ∈ s, f i ^ n i - ∏ i ∈ s, g i ^ n i` has order at least the natural number
`∑ i ∈ s, n i + 1`, cast to `ℕ∞`. For empty `s` the difference is `1 - 1 = 0`.
All four hypotheses are those of the source and concern only indices in `s`.

## Checks

With environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), the module compiles without
warnings and the inspection of each of the six declarations reports
`statement_returns_prop: true`. As a shape check (a private draft, not part of
this module), the six source proofs, with an opening `unfold d00kStatement`
added where the first tactic needs the unfolded goal and the calls to the
private helpers replaced by the corresponding `d00k`, compile against these
targets as theorems `theorem d00k <source telescope> : d00kStatement <binders>`.
`Finsupp.degree d` is by definition `∑ i ∈ d.support, d i`
(`Finsupp.degree_apply`), and the zero-constant-coefficient reading of
`1 ≤ f.order` is Mathlib's `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero`.

## License

The Lean file keeps the original copyright, Apache-2.0 license and author
header and records the modifications. The original `LICENSE` and `NOTICE` are
in the Library at `licenses/NYLL/`.
