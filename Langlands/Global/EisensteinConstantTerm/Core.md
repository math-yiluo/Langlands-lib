# The unfolding computation behind the constant-term formula

Module `Langlands.Global.EisensteinConstantTerm.Core`. It formalizes the computation in the
proof of Bernstein–Lapid Lemma 6.10 (6.17) (J. Bernstein and E. Lapid, J. Amer. Math. Soc. 37
(2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal
p. 208, PDF page 22). It runs from the Eisenstein series to the integrals over
`(U_Q ∩ wPw⁻¹)(F) \ U_Q(A)`, for an abstract function `Φ` in place of `φ_λ`. The last
identification, with the intertwining integrals, is an abstract hypothesis here. Throughout,
`V(𝔸)` is the group of adelic points of `range (iV ≫ q)`, `V(F)` is its principal subgroup, and
`μ_V` is the Library's `normalizedHaarMeasure`: Haar measure multiplied by the reciprocal of the
total mass of `V(F) \ V(𝔸)`. The unfolding results below assume that `V(F) \ V(𝔸)` is compact
(a `CompactSpace` instance), so that mass is finite and nonzero, and `μ_V` gives
`V(F) \ V(𝔸)` mass one. In the reduction, `V` is a unipotent radical, and compactness comes from
`AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent`.

## Conjugation (`section Conj`)

- `conjAdelic q iV hN x`: for `x ∈ Q(𝔸)` and `V` normal in `Q`, conjugation `v ↦ q(x) v q(x)⁻¹`
  as a continuous group automorphism of `V(𝔸)` (`conj_mem_adelicPoints_range`). The lemma
  `conjAdelic_coe` evaluates it.
- `conjAdelic_mem_rationalSubgroup_iff`: for `x` rational, it preserves `V(F)`
  (`conj_mem_rationalImage` applied to `q(x)` and `q(x)⁻¹`).

## Measures (`section Setup`)

- `instLocallyCompactSpaceAdelicPoints`: closed adelic subgroups are locally compact.
- `normalizedRationalQuotientHaarMeasure_eq_quotientMeasure`: a push-forward identity for the
  mass-normalized measures, for any closed adelic subgroup `U`. The Library's
  `normalizedRationalQuotientHaarMeasure` on `U(F) \ U(𝔸)` is the push-forward of
  `normalizedHaarMeasure` restricted to the chosen fundamental domain
  `LeftCosetSpace.fundamentalDomain`. Both are scaled by the same factor
  `quotientMassNormalizer`, the reciprocal of the total Haar mass of `U(F) \ U(𝔸)`. The lemma
  assumes no finiteness. The measure is a probability measure only when that mass is finite,
  for instance when `U(F) \ U(𝔸)` is compact (the Library's
  `normalizedRationalQuotientHaarMeasure_isProbabilityMeasure`). If the mass is infinite, both
  measures are zero.
- `haar_fundamentalDomain_eq`, `haar_fundamentalDomain_ne_zero`, `haar_fundamentalDomain_ne_top`:
  the Haar measure of that fundamental domain is the total mass of `U(F) \ U(𝔸)`. It is nonzero,
  and finite when the quotient is compact.
- `countable_rationalSubgroup`: `U(F)` is countable, being discrete in a second-countable group.
- `instIsClosedAdelicPointsRange` (instance): the adelic points of the range of a closed
  immersion `iV ≫ q` form a closed subgroup. `normalizedHaarMeasure_isMulLeftInvariant`: the
  normalized Haar measure is left invariant. `countable_rationalSubgroup_ambient`: `G(F)` is
  countable.

## Removing the conjugation and unfolding (`section Unfold`)

`unfold_conj` takes the following data:

- `γ = q(x₀)` with `x₀ ∈ Q(F)`, a point `w ∈ G(𝔸)`;
- representatives `ρ'` of `(V(F) ∩ wP(F)w⁻¹) \ V(F)` inside `V(𝔸)`;
- a continuous left `P(F)`-invariant `Φ`, and `g ∈ G(𝔸)`.

Let `s` be the chosen fundamental domain of `V(F)`. The lemma proves

`∫⁻_{(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)} ‖Φ(w⁻¹ x̄ γ g)‖ₑ = ∫⁻_{v ∈ s} ∑'_ν ‖Φ(w⁻¹ ρ'_ν γ v g)‖ₑ dμ_V`

for `stabilizerMeasure`. When this is finite, it proves the same identity for the integrals of
`Φ` itself. Proof:

1. `α = conjAdelic q iV hN x₀` preserves `V(F)`. By `measurePreserving_of_preserves` it preserves
   `μ_V`, so `∫_s K(α v) = ∫_{α.symm⁻¹ s} K`, and `α.symm⁻¹ s` is again a strict fundamental
   domain of `V(F)`.
2. Pointwise, `Φ(w⁻¹ ρ' γ v g) = f(ρ' α(v))` with `f(v) = Φ(w⁻¹ v γ g)`. The function `f` is left
   invariant under `V(F) ∩ wP(F)w⁻¹`, because `Φ` is left `P(F)`-invariant.
3. `lintegral_unfold` and `integral_unfold` on the fundamental domain `⋃ ρ'_ν α.symm⁻¹ s` of
   `V(F) ∩ wP(F)w⁻¹`, together with `LeftCosetSpace.discreteQuotientMeasure_eq`, which
   identifies `stabilizerMeasure` with the quotient measure built on this fundamental domain.

## The computation (`section Main`)

`constantTerm_series_eq` takes the following data:

- `IsDoubleCosetRepresentatives F q p w` for a finite family `w`;
- subgroups `Q'_i = (Q(F) ∩ w_iP(F)w_i⁻¹) ⊔ V(F)`;
- `V` normal in `Q`, with `V(F) \ V(𝔸)` compact;
- a continuous left `P(F)`-invariant `Φ`, a point `g`, and a bound
  `∑'_{c ∈ P(F) \ G(F)} ‖Φ(c̄ v g)‖ₑ ≤ B₀ < ∞` for all `v ∈ V(𝔸)`;
- numbers `R i y` and propositions `Int i y`, together with `hB`: whenever
  `∫⁻ ‖Φ(w_i⁻¹ x̄ y)‖ₑ` over `(V(F) ∩ w_iP(F)w_i⁻¹) \ V(𝔸)` is finite, `Int i y` holds and
  `R i y = ∫ Φ(w_i⁻¹ x̄ y)` over the same quotient.

The conclusions are:

1. `Int i (γ_c g)` for every `i` and `c ∈ Q'_i \ Q(F)`;
2. `c ↦ R i (γ_c g)` is summable for every `i`;
3. `subgroupConstantTerm F (iV ≫ q) (x ↦ ∑'_{c ∈ P(F) \ G(F)} Φ(c̄ x)) g = ∑_i ∑'_c R i (γ_c g)`.

Proof:

- The hypotheses give `BruhatData` with `P` in the form `(rationalSubgroup F P).map p`, so that
  `P \ Gr` is literally `ParabolicRationalCosets F p`.
- For each `j = (i, c)` put `L_j(v) = ∑'_ν ‖Φ(w_i⁻¹ ρ'_ν γ_c v g)‖ₑ` and let `G_j(v)` be the same
  sum without norms.
- By `tsum_out_eq_tsum_bruhat` and `ENNReal.tsum_sigma'`,
  `∑'_{c ∈ P(F) \ G(F)} ‖Φ(c̄ v g)‖ₑ = ∑'_j L_j(v) ≤ B₀`. Hence `∑'_j ∫⁻_s L_j ≤ B₀ μ_V(s) < ∞`.
- `unfold_conj` identifies `∫⁻_s L_j` with the lower integral in `hB`, so `hB` applies. With
  `unfold_conj` again it gives `Int` and `R i (γ_c g) = ∫_s G_j`. Then
  `‖R i (γ_c g)‖ₑ ≤ ∫⁻_s L_j`, which gives summability over `j` and, by `Summable.sigma_factor`,
  over each `c`.
- For the constant term:
  - `x ↦ ∑'_c Φ(c̄ x)` is left `G(F)`-invariant (`tsum_out_mul_left`), so the constant term
    equals `∫_s ∑'_c Φ(c̄ v g) dμ_V` (`integral_out_eq`).
  - Pointwise, the summability from the bound gives `∑'_c Φ(c̄ v g) = ∑'_j G_j(v)` (Bruhat
    reindexing and `Summable.tsum_sigma`).
  - `integral_tsum` exchanges the integral with the sum over `j`, dominated by `∑'_j ∫⁻_s L_j`.
  - `Summable.tsum_sigma` and `tsum_fintype` split the sum over `j` into `∑_i ∑'_c`.

## Provenance

This is the computation of BL p. 208 (first three displays) and of Mœglin–Waldspurger II.1.7
(*Spectral decomposition and Eisenstein series*, 1995, registered as
`moeglin-waldspurger-1995-spectral-decomposition`, printed pp. 91–93). BL justify the exchange of
sum and integral by the range of convergence. MW justify it by bounding the same expression with
`|φ|`. Here the bound is the hypothesis `hS`. The formalization is internal.
