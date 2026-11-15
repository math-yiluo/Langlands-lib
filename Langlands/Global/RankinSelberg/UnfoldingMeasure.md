# Measure-theoretic unfolding lemmas for discrete left quotients

Internal helper module for the conditional reduction
`Langlands.Global.RankinSelbergGlobal.UnequalUnfoldingReductionStatement`
(see `UnequalUnfoldingReduction.md`). It contains general measure
theory on a group `H` with subgroups; none of it is specific to
general linear groups. Provenance: internal; standard unfolding and
Weil-averaging arguments, proved here from Mathlib.

## Sum unfolding (`SumUnfolding`)

Let `Λ ≤ Γ ≤ H`, let `s` be a strict fundamental domain of `Γ` (every
`x` has exactly one `γ ∈ Γ` with `γx ∈ s`), and let `ρ : ι → H` be
representatives of `Λ \ Γ` (every `γ ∈ Γ` lies in exactly one coset
`Λ ρ(i)`).

- `existsUnique_mem_iUnion_smul`: `⋃ i, ρ i • s` is a strict
  fundamental domain of `Λ`.
- `pairwise_disjoint_smul`: the translates `ρ i • s` are pairwise
  disjoint.
- `integrableOn_tsum_and_setIntegral_eq` (lemma A): for a left-invariant
  measure and `ι` countable, if `f` is integrable on `⋃ i, ρ i • s`, then
  `x ↦ Σ' i, f(ρ i x)` is integrable on `s` and
  `∫_s Σ' i, f(ρ i x) dx = ∫_{⋃ ρ i • s} f`.

## Weil averaging (`Averaging`, `AveragingIntegral`)

For a countable `Λ ≤ N ≤ H`, strict fundamental domains `sH` of `Λ` in
`H` and `sN` of `Λ` in `N`, a left-invariant s-finite measure on `H`
and a left- and inversion-invariant s-finite measure `ν` on `N`:

- `isFundamentalDomain_slice`: each slice `{n : n x ∈ sH}` is a
  fundamental domain of `Λ` in `N`.
- `lintegral_average` (nonnegative form) and
  `integrable_and_integral_average` (lemma B'): for `F` measurable,
  left `Λ`-invariant and integrable on `sH`, `(n, x) ↦ F(n x)` is
  integrable on `sN × sH` and its integral equals `ν(sN) ∫_{sH} F`
  (the latter needs `ν(sN) < ∞`).

## Quotient representatives (`Representatives`, `CosetRepresentatives`)

- `out_eq_lift`, `exists_out_mk_eq`: evaluating a left-invariant
  function at chosen representatives is its descent; the chosen
  representative of the class of `x` is `γ x` for some `γ`.
- `integrable_out_iff`, `integral_out_eq`: for the quotient measure
  `quotientMeasure Γ ν s` (the push-forward of `ν` restricted to `s`),
  integrability and integral of `q ↦ f(q.out)` are those of `f` on `s`.
- `cosetRep`, `cosetRep_mem`, `existsUnique_cosetRep`: representatives
  `cosetRep Λ Γ q ∈ Γ` of the right cosets
  `Quotient (QuotientGroup.rightRel (Λ.subgroupOf Γ))`, with each
  `γ ∈ Γ` in exactly one coset.
