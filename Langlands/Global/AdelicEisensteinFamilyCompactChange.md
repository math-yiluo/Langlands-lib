# The family comparison under a finite change of the Iwasawa compact

Module `Langlands.Global.AdelicEisensteinFamilyCompactChange` proves that
`FamilyRegularComparison` (module `Langlands.Global.AdelicEisensteinFamilyRegularComparison`)
passes from one maximal compact subgroup to another with the same infinite projection. It also
contains three auxiliary results.

## Auxiliary results

- `Langlands.Analysis.Meromorphic.IsMeromorphicInCoordinatesOn.mul_exp`: if `b` is meromorphic
  in linear coordinates with domain of holomorphy `D`, and `ℓ` is a complex linear form, then
  `x ↦ b x · exp (ℓ x)` is meromorphic with the same domain. In every coordinate system the
  exponential factor is holomorphic on the whole space and nonvanishing; the product rule for
  meromorphic functions in coordinates (`(hb.2 n e).mul`) gives the claim.
- `complexParameterPairingAt v`: the complex linear form `λ ↦ ⟨λ, v⟩` on `X^*(H) ⊗ ℂ` given by
  `complexParameterPairing` at a fixed real dual vector `v`.
- `IsMaximalCompactSubgroup.comap_ofInfinite_eq_of_infinite_eq`: maximal compact subgroups `K`,
  `L` of `G(𝔸)` with the same image under the projection `infinite F G` to the archimedean
  points have the same archimedean part `K.comap (ofInfinite F G)`. For a maximal compact
  subgroup the archimedean part equals the infinite projection (`IsMaximalCompactSubgroup.mem_iff`).

## Main theorem

`FamilyRegularComparison.of_finiteCompactChange`: let `G` be connected reductive, `iU`, `iV`
geometric unipotent radicals, `q` parabolic with rational Levi `l'` and Levi-first
multiplication `M' × V → Q` an isomorphism, `(w, c)` a Weyl conjugation from `P` to `Q`, and
`rho` closed. Let `K`, `L` be maximal compact subgroups of `G(𝔸)`, both with Iwasawa coverage
for `P` and `Q`, with the same infinite projection. Then
`FamilyRegularComparison.{u, max v u, max w u}` for `L` implies
`FamilyRegularComparison.{u, v, w}` for `K`.

### Proof

Fix the data `φ, b, EP, ψ, coeff` for `K`.

1. For each `φ x`, `eisensteinFiniteCompactOperatorComparison` (module
   `Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison`) gives a finite set `S x`
   of real dual vectors, functions `cut x u` automorphic for `L`, and a threshold `Rc x` beyond
   which `E_K(φ x, λ) = ∑ u ∈ S x, exp⟨λ, u⟩ · E_L(cut x u, λ)` and the parameter twist of
   `M_K(w, λ)(φ x)` is the corresponding sum of twists of `M_L(w, λ)(cut x u)`.
2. For each `ψ i`, `eisensteinFiniteCompactChange` (module
   `Langlands.Global.AdelicEisensteinFiniteCompactChangeProof`) gives a finite set `S' i` and
   functions `cut' i u` automorphic for `K_∞ = L_∞` with
   `twist_K(ψ i, μ) = ∑ u ∈ S' i, exp⟨μ, u⟩ · twist_L(cut' i u, μ)` for every `μ`.
3. The new data for `L` are indexed by the sigma types `Σ x, S x` and `Σ i, S' i`:
   `φ' ⟨x, u⟩ = cut x u` with coefficient `b x λ · exp⟨λ, u⟩`, and `ψ' ⟨i, u⟩ = cut' i u` with
   coefficient `coeff i λ · exp⟨wλ, u⟩`. The coefficients are meromorphic by `mul_exp`. The
   index types live in `max v u` and `max w u`.
4. The hypotheses for `L` follow above the threshold `max R₁ (∑ x, |Rc x|)`: the series
   identity by step 1, and the intertwining identity after multiplying both sides by the
   nonvanishing height factor at `wλ` for `L`, using steps 1 and 2 and the hypothesis for `K`.
5. The predicate for `L` is applied with threshold `max R (∑ z, |RQ z|)`, where `RQ z` is a
   summability threshold for the `Q`-series of `ψ' z`
   (`EisensteinAbsoluteConvergenceStatement.exists_summable_eisensteinTerm` applied to
   `eisensteinAbsoluteConvergence`). On the resulting patch, the `Q`-series for `K` of each
   `ψ i` is rewritten as the finite sum over `S' i` of `Q`-series for `L`
   (`IsIwasawaCompact.eisensteinSeries_eq_finset_sum_of_twist`), which is the conclusion for
   `K`.

## Source

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, work with one maximal compact
subgroup in good position. This module lets the comparison pass to any maximal compact
subgroup with the same archimedean component, using the Library's comparison of Eisenstein
series and intertwining operators for two such compacts.
