# Power coefficients after adding one monomial: targets M351.021–M351.023

This module states the types of the three source-private theorems M351.021,
M351.022 and M351.023 as proposition definitions. It proves none of them.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
Its SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
It is readable in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright, Apache-2.0 and author header is preserved in the Lean
file, followed by a dated modification notice. The existing
[NYLL license](../../../../../../../licenses/NYLL/LICENSE) and
[NYLL notice](../../../../../../../licenses/NYLL/NOTICE) apply unchanged.
No patch10 edit affects this source module.

## Exact targets

All three targets are in `Langlands.NYLL.PortInternal.M351`. Each takes the
complete binder list of its source theorem, in source order, with source
binder kinds and names, and has the source conclusion as its body.
Each source declaration has its own `{R : Type*}` and `{τ : Type*}`, so the
coefficient and variable universes are independent (`u_1` and `u_2`); `R` is
an arbitrary commutative ring (`[CommRing R]`) and `τ` an arbitrary type of
variables, with no finiteness, decidability, nontriviality or local-field
assumption.

| Unit | Source lines | Source name | Target |
| --- | --- | --- | --- |
| M351.021 | 604–610 (type 604–607) | `LubinTate.SameUniformizer.constantCoeff_monomial_eq_zero_stabilization` | `d021Statement` |
| M351.022 | 612–680 (type 612–620) | `LubinTate.SameUniformizer.coeff_pow_add_monomial_sub_pow_of_degree_le` | `d022Statement` |
| M351.023 | 682–696 (type 682–691) | `LubinTate.SameUniformizer.coeff_pow_add_monomial_of_degree_le` | `d023Statement` |

### M351.021

`d021Statement {R} [CommRing R] {τ} {d : τ →₀ ℕ} (hd : d ≠ 0) (c : R)` is

```
MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0
```

that is, the monomial `c X^d` with nonzero exponent `d` has zero constant
coefficient.

### M351.022

`d022Statement {R} [CommRing R] {τ} {H : MvPowerSeries τ R}
(hH : MvPowerSeries.constantCoeff H = 0) (q d : τ →₀ ℕ)
(hq : q.degree ≤ d.degree) (hd : 1 ≤ d.degree) (c : R) (n : ℕ)` is

```
MvPowerSeries.coeff q ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
  if n = 1 then (if q = d then c else 0) else 0
```

So, for `H` with zero constant coefficient and a monomial of total degree
`d.degree ≥ 1`, every coefficient of `(H + c X^d) ^ n - H ^ n` in an exponent
`q` of total degree at most `d.degree` vanishes, except that for `n = 1` the
coefficient at `q = d` is `c`. The term `c` appears only under both conditions
`n = 1` and `q = d`, exactly as in the source. Here `q.degree` and `d.degree`
are Mathlib's `Finsupp.degree`, the sum of the exponents.

### M351.023

`d023Statement` has the same binders as `d022Statement` and body

```
MvPowerSeries.coeff q ((H + MvPowerSeries.monomial d c) ^ n) =
  MvPowerSeries.coeff q (H ^ n) +
    if n = 1 then (if q = d then c else 0) else 0
```

the same fact after moving `H ^ n` to the right-hand side.

### Decidability

The source module sets `attribute [local instance] Classical.propDecidable`
(line 31). This module sets the same local attribute, so the two `if`
conditions elaborate with the source's instances: `n = 1` with
`instDecidableEqNat`, and `q = d` with `Finsupp.instDecidableEq`, whose
equality decision on `τ` is `Classical.propDecidable`. No global or scoped
instance is added. A development check in the same environment, under the
source's local attribute and its `Mathlib.RingTheory.MvPowerSeries.Trunc`
import, confirmed by reducible `rfl` that each source type, transcribed
verbatim with universes `u` and `v`, equals the universally quantified target.

## Adaptations

The following are all modifications to the selected source declarations:

- Split the three theorem types from the original combined module into this
  focused statement module.
- Replace each private theorem by a public reducible `abbrev` returning `Prop`,
  named by the stable internal name `d021Statement`, `d022Statement` or
  `d023Statement` in namespace `Langlands.NYLL.PortInternal.M351`, in place of
  the source namespace `LubinTate.SameUniformizer`.
- Omit the proofs. Retain the source hypothesis names; since the proposition
  bodies do not use the hypotheses, each definition locally disables the
  unused-variables linter.
- Omit the source section variables `K`, `F`, `π`, `σ` and `[Fintype σ]`
  (source lines 68–70). They do not occur in these theorems, so Lean did not
  include them in the source theorems' types.
- Replace the imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`
  and `Mathlib.RingTheory.MvPowerSeries.Trunc` by
  `Mathlib.RingTheory.MvPowerSeries.Basic`, which supplies
  `MvPowerSeries.monomial`, `MvPowerSeries.coeff`,
  `MvPowerSeries.constantCoeff` and `Finsupp.degree`. NYLL adds no global
  decidability instance, so the instance choice above does not depend on the
  omitted import.
- Omit the unused `noncomputable section`, `open scoped BigOperators`,
  `universe u v w` and `open LocalFieldTheory.DiscreteValuationField`
  (source lines 28, 30, 33 and 38), and
  replace the module exposition by statement-specific documentation.

## Proof boundary

In the source, M351.021 rewrites the constant coefficient as the coefficient
at `0` and applies `MvPowerSeries.coeff_monomial_ne`. M351.022 uses M351.021
together with the source-private order estimates M351.005 (a monomial has
order at least its total degree) and M351.009 (the order of a difference of
powers), owned by Task 6075 at `Langlands.NYLL.PortInternal.M351.d005` and
`d009`, to show that for `n ≥ 2` the difference has order at least
`d.degree + 1`; the case `n = 1` is a direct coefficient computation and
`n = 0` is trivial. M351.023 rearranges M351.022. These remarks only identify
later work: each exact theorem `Langlands.NYLL.PortInternal.M351.d021`,
`d022` and `d023` is to be routed to its own `lean.proof@1` task after this
target is published. The local-field coefficient response M351.024 and
later units consume these theorems.

## Development verification

The module compiled in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) without warnings or errors.
Exact-declaration inspections of the three targets reported
`statement_returns_prop: true`. Development compilation and inspection do not
establish independent semantic acceptance or prove any target.
