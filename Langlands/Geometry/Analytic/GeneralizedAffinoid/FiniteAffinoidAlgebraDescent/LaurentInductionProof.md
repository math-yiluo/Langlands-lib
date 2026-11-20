# Proof of induction along iterated real-radius binary Laurent splits

`Langlands.Analytic.PresentedAffinoidAlgebra.finiteCoverBinaryLaurentInduction`
proves `FiniteCoverBinaryLaurentInductionStatement`. The only axioms it uses are
`propext`, `Classical.choice` and `Quot.sound`.

## Overview

The proof builds a finite tree of tests on the spectrum `X` of `R`. A test is a
triple `(f, g, ρ)` with `f, g ∈ R` and `ρ > 0`, with `g` nonvanishing on the
current node `S`. It splits `S` into `S ∩ {|f| ≤ ρ|g|}` and
`S ∩ {ρ|g| ≤ |f|}`. Each leaf of the tree lies in the locus of some cover member
or is empty. On a full domain `U` whose locus lies in `S`, the image of `g` is a
unit. With `a = f g⁻¹`, the two halves of the test become the binary Laurent
halves `{|a| ≤ ρ}` and `{|a| ≥ ρ}` of the statement. The step hypothesis then
carries the predicate `P` up the tree.

The tree comes from the Library's rational refinement of the cover. A
"products" argument then splits the spectrum by tests until each piece lies in
one rational chart. All radii are arbitrary positive reals, so the argument
needs no scalar of small nonzero absolute value. It works over trivially valued
fields and for non-strict `R`.

## Spectrum and real-number helpers (namespace `LaurentInduction`)

- `spec_one`, `spec_mul`, `spec_nonneg`, `spec_prod`: a point of
  `BanachSpectrum A` is a multiplicative seminorm, so it sends `1` to `1`, is
  multiplicative (also over finite products) and is nonnegative.
- `exists_max_of_total`: a transitive relation that is total on a nonempty
  finset has an element dominating all others (Finset induction).
- `exists_prod_pos`: let `φ k j ≥ 0` be indexed by charts `k` and entries
  `j ∈ Fin (m k + 1)`. Suppose every family `φ k` has a positive entry, and the
  zeroth entry of family `k0` is its largest. Then some tuple `μ` with
  `μ k0 = 0` has `∏ₖ φ k (μ k) > 0`. Take a positive entry in each family and
  replace the `k0` coordinate by `0`.
- `le_zero_of_isMax`: same hypotheses on `φ` and `k0`, plus nonnegativity. If
  `ν k = 0` and `∏ φ(ν)` is at least `∏ φ(μ)` for every tuple `μ` with
  `μ k0 = 0`, then `φ k j ≤ φ k 0` for every `j`. Otherwise, let `J` choose a
  largest entry in each family. The tuple `J` with its `k0` coordinate replaced
  by `0` has product at least `∏ φ(J)`. But `∏ φ(ν) < ∏ φ(J)`. Either every
  factor of `ν` is positive and the `k`-th factor is strictly below `φ k j`, or
  some factor is `0` and `∏ φ(J) > 0`. This contradicts maximality.
- `le_mul_iff_div_le`, `mul_le_iff_div_le`: rearrange `p ≤ (a/b) q` and
  `(a/b) q ≤ p` as `p/a ≤ q/b` and `q/b ≤ p/a` for `a, b > 0`.

## Test trees

- `lowerSide f g ρ = {x | x f ≤ ρ * x g}` and
  `upperSide f g ρ = {x | ρ * x g ≤ x f}`.
- `Fine Q S` is an inductive predicate on subsets of the spectrum. A leaf is a
  set satisfying `Q`. A `split f g ρ` of `S` needs `0 < ρ`, `g` nonvanishing at
  every point of `S`, and `Fine Q` on both `S ∩ lowerSide f g ρ` and
  `S ∩ upperSide f g ρ`.
- `prop_of_fine`: assume the base hypothesis in the form "`Q S` and
  `U.locus ⊆ S` give `P U`", and assume the step hypothesis of the statement.
  Then `Fine Q S` gives `P U` for every full domain `U` with `U.locus ⊆ S`. The
  proof is induction on `Fine`. At a split, every point of `U`'s spectrum maps
  into `S`, where `g` does not vanish. So `U.baseMap g` is a unit by
  `isUnit_iff_forall_spectrum_ne_zero`. For `a = U.baseMap f * u⁻¹` and every
  point `y` we have `y a · y(U.baseMap g) = y(U.baseMap f)`. Hence
  `{y | y a ≤ ρ}` maps into `S ∩ lowerSide f g ρ` and `{y | ρ ≤ y a}` maps into
  `S ∩ upperSide f g ρ`. Then the induction hypotheses give `P U₁` and `P U₂`,
  and the step hypothesis gives `P U`.
- `fine_of_tests`: suppose a finite family of tests has positive radii and
  denominators nonvanishing on `S`. If `Fine Q C` holds for every `C ⊆ S` lying
  on one side of every test, then `Fine Q S` holds. The proof splits along the
  tests one by one (Finset induction).

## The products argument (`fine_univ_of_charts`)

The setting is finitely many charts `k : Fin n`, each with elements
`h k j ∈ R` and weights `w k j > 0` for `j : Fin (m k + 1)`. Write
`φ k j (x) = x(h k j) / w k j`. The chart set of `k` is
`{x | ∀ j, φ k j x ≤ φ k 0 x}`. The hypotheses are:

- `Q` is monotone and `Q ∅` holds;
- the chart sets cover the spectrum;
- no family `h k` has a common zero;
- `Q` holds on every chart set.

The conclusion is `Fine Q univ`.

For a tuple `ν` of entries, set `prodElt h ν = ∏ₖ h k (ν k)` and
`prodWt w ν = ∏ₖ w k (ν k)`. Then
`Φ_ν(x) = x(prodElt h ν) / prodWt w ν = ∏ₖ φ k (ν k) x`. Let `N` be the finset
of tuples with at least one zero coordinate.

1. **Threshold.** Every point `x` has some `μ ∈ N` with `Φ_μ(x) > 0`. Apply
   `exists_prod_pos` with `k0` a chart containing `x`. If the spectrum is
   nonempty, the continuous function `G = ∑_{μ ∈ N} Φ_μ` attains a minimum
   `G(x₀) > 0` on the compact spectrum. With `c = G(x₀)/(|N| + 1)`, every point
   has some `μ ∈ N` with `Φ_μ(x) > c`. If the spectrum is empty, take `c = 1`.
2. **Stage one.** Apply `fine_of_tests` with the tests
   `(prodElt h ν, 1, c · prodWt w ν)` for `ν ∈ N`; the denominator `1` never
   vanishes. These tests compare each `Φ_ν` with `c`. On a resulting piece `C`,
   let `T` be the tuples `ν ∈ N` for which `C` is not on the lower side. Then
   `Φ_ν ≥ c` on `C` for `ν ∈ T` and `Φ_ν ≤ c` on `C` for `ν ∈ N \ T`.
3. **Stage two.** Apply `fine_of_tests` inside `C` with the tests
   `(prodElt h μ, prodElt h ν, prodWt w μ / prodWt w ν)` for
   `(μ, ν) ∈ T × T`. Their denominators do not vanish on `C` because
   `Φ_ν ≥ c > 0` there. On a resulting piece `C'`, the relation "`Φ_μ ≤ Φ_ν` on
   all of `C'`" is transitive and total on `T`.
   - If `T` is empty, `C'` is empty: every point has some `μ ∈ N` with
     `Φ_μ > c`, but all `Φ_μ ≤ c` on `C`. So `Q C'` follows from `Q ∅` and
     monotonicity.
   - Otherwise `exists_max_of_total` gives a dominating `ν ∈ T`. Some coordinate
     `ν k` is `0`. Let `x ∈ C'` and let `k0` be a chart containing `x`. Every
     tuple `μ` with `μ k0 = 0` lies in `N`. Either `μ ∈ T`, so
     `Φ_μ(x) ≤ Φ_ν(x)` by dominance, or `Φ_μ(x) ≤ c ≤ Φ_ν(x)`. Now
     `le_zero_of_isMax` puts `x` in the chart set of `k`. So `C'` lies in that
     chart set, and `Q C'` follows by monotonicity.

## Rational charts

- `chartElt d` is the denominator of a rational chart `d` followed by its
  numerators (`Fin.cons`). `chartWt d` is `1` followed by the radii.
  `chartWt_pos` holds because the radii are positive.
- `mem_locus_iff`: `x ∈ d.locus` iff `x` lies in the chart set of
  `(chartElt d, chartWt d)`. This unfolds
  `|numerator j| ≤ r_j · |denominator|`.
- `exists_chartElt_ne_zero`: the field `d.generates` says that the denominator
  and numerators span the unit ideal. By the Library's
  `span_range_eq_top_iff_forall_spectrum_exists_ne_zero`, some `chartElt d j`
  does not vanish at any given point.

## Main theorem

Let `Q S` be `∃ i, S ⊆ (c.obj i).locus`. Let `r = c.relativeRationalRefinement`;
this Library construction is built on the published finite rational coverage of
domains. Its charts `r.chart k` cover the spectrum (`r.covers`). The locus of
each chart lies in the locus of `c.obj (r.index k)`, by the inclusion `r.map k`
of the extended chart domain (`Domain.extend_locus`,
`RationalChart.toDomain_locus`). `fine_univ_of_charts` with
`h k = chartElt (r.chart k)` and `w k = chartWt (r.chart k)` gives
`Fine Q univ`. Here `Q ∅` holds because `0 < c.size` provides a member. Then
`prop_of_fine` with the base hypothesis of the statement gives
`P (Domain.whole K R)`, since the locus of the whole domain lies in `univ`.

## Provenance

This proof is an internal derivation. Its overall shape follows the classical
reduction of a finite affinoid covering to binary Laurent splits in the proof of
Tate's acyclicity theorem: Piotr Achinger, *Introduction to non-Archimedean
Geometry*, lecture notes, November 22, 2020, §7.2–§7.3, pp.65–67 (registered
source `achinger-2020-non-archimedean-geometry-nov22`). That proof first refines
to a rational covering by Gerritzen–Grauert, then splits by binary Laurent
coverings.

The combinatorial step implemented here is different. Achinger inducts on the
number of non-units among the generators `f₀, …, fₙ` of one rational covering,
using a scalar `t` with `|t^N|` small. Here the chart functions of all
refining rational charts are multiplied into the products `Φ_ν`. Then a positive
real threshold from compactness of the spectrum and pairwise comparisons of
the products produce the tree. This avoids small scalars and the separate
treatment of trivially valued fields.

The Library inputs are `Domain.FiniteCover.relativeRationalRefinement`
(module `DomainRelativeRationalRefinement`), the spectral unit criterion
`isUnit_iff_forall_spectrum_ne_zero`, the spectral ideal criterion
`span_range_eq_top_iff_forall_spectrum_exists_ne_zero`
(`SpectrumIdealCriterionProof`), compactness of the Banach spectrum, and the
rational chart API (`RationalChartDomain`).
