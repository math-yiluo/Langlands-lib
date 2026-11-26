# The limit of `(G, M)`-family integrals along orthogonal sets

Module `Langlands.LinearAlgebra.GMFamilyOrthogonalSetLimitStatement` states
Lapid's Lemma 8 in the abstract setting of
[`Langlands.LinearAlgebra.GMFamilies`](GMFamilies.md):
`Langlands.GMFamily.OrthogonalSetLimitStatement`. It does not prove it.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9):
  - §7, p.326: the `(G, M)`-family `c_Q(T; λ) = e^{⟨λ, Y_Q(T)⟩}`, the
    inequality (15) `⟨α, Y_Q(T)⟩ ≥ c‖T‖` for `T` in the cone `C` and
    `α ∈ Δ_Q`, and Lemma 8: "For any `n` there exists a continuous seminorm
    `μ_n` on the space of Schwartz functions on `i𝔞_P^*` such that for any
    `(G, M)`-family `d_Q(λ)` consisting of Schwartz functions and `T ∈ C` we
    have `|∫_{i(𝔞_P^G)^*} ∑_{Q ∈ 𝓟(M)} c_Q(T; λ) d_Q(λ) / θ_Q(λ) dλ − d_P(0)|
    ≤ (1 + ‖T‖)^{-n} ∑_{Q ∈ 𝓟(M)} μ_n(d_Q)`";
  - pp.326–327: its proof, which uses of `Y(T)` only (15), the formula for
    `c_M^{Q₁}(T; μ)` as the Fourier transform of the characteristic function of
    a convex hull, and the polynomial growth in `T` of these convex hulls;
  - §8, p.328: its use in the proof of Proposition 2.
- J. Arthur, *An introduction to the trace formula* (2005), §17, in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, printed pp.94–95
  (PDF pp.106–107): positive `(G, M)`-orthogonal sets
  (`Y_P − Y_{P'} = r_α α^∨`, `r_α ≥ 0`, for `P`, `P'` adjacent along
  `α ∈ Δ_P`), the `(G, M)`-family (17.2) `c_P(λ, Y) = e^{λ(Y_P)}`, (17.3) and
  Lemma 17.2.

## Definitions

- `IsPositiveOrthogonalSet R a Y`: `Y : Finset E → a` assigns to each chamber
  `S ∈ parabolics R a` (the groups `P ∈ 𝓟(M)`) a point `Y S ∈ 𝔞_M`, and
  `Y S − Y S' = r • v` with `r ≥ 0` whenever `IsAdjacentAlong R a S S' v`.
  Arthur's `α^∨` is replaced by the vector `v` of `a` of the restricted root,
  a positive multiple of `α^∨` for the inner product, so the condition is
  Arthur's.
- `relativeSpace R a = a ⊓ (centralSpace R)ᗮ`, the space `𝔞_M^G`.
- `dualParam R a x`, for `x ∈ 𝔞_M^G`: the functional `H ↦ ⟪x, H⟫` on
  `a = 𝔞_M`. Every point of `i(𝔞_M^G)^*` is `iΛ_x` for exactly one `x`.

## The statement

`OrthogonalSetLimitStatement` (universe `u` of `E`): let `E` be a
finite-dimensional real inner product space (with its Borel σ-algebra), `R` a
root set in `E` (`IsRootSet`) and `a` a Levi space (`IsLeviSpace R a`). For
all `n : ℕ` and `κ : ℝ` there are a finite set `s` of indices of Schwartz
seminorms and a constant `C` with the following property. Let `d` assign to
each chamber a Schwartz function `d S` on `StrongDual ℝ a` (the points `λ = iΛ`
of `i𝔞_M^*`) forming a `(G, M)`-family (`IsFamily`), let `t ≥ 0`, and let `Y`
be a positive `(G, M)`-orthogonal set with `⟪v, Y S⟫ ≥ t` for every chamber
`S` and every `v ∈ simpleRoots a S`, and `‖Y S‖ ≤ κ(1 + t)` for every chamber.
Then for every chamber `S₀`

```
‖ (2π)^{-k} ∫_{x ∈ 𝔞_M^G} c_M(iΛ_x) dx − d_{S₀}(0) ‖
    ≤ C / (1 + t)^n · ∑_S (s.sup schwartzSeminormFamily)(d S),
```

where `k = dim 𝔞_M^G`, `dx` is the volume of the inner product space
`𝔞_M^G` (the Haar measure giving an orthonormal parallelepiped volume `1`),
and `c_M = cM R a (fun S Λ => exp(i Λ(Y S)) · d S Λ)`, that is,
`c_M(λ) = ∑_P e^{λ(Y_P)} d_P(λ) θ_P(λ)⁻¹`.

### Correspondence with Lapid

- Lapid's measure `dλ` on `i(𝔞_P^G)^*` is dual to the measure `dH` on
  `𝔞_P^G`: his proof uses `φ_P(H) = ∫ e^{⟨μ, H⟩} d_P(μ) dμ` and
  `∫ φ_P(H) dH = d_P(0)` (17). With `dH` the Euclidean measure, which is the
  measure in `θ_Q` (the Library's `theta` uses Gram volumes), the dual measure
  in the coordinates `x` is `(2π)^{-k} dx`.
- In the definition of `cM`, `θ_P(Λ)⁻¹` is `0` where `θ_P(Λ) = 0`. On
  `i(𝔞_M^G)^*` these points lie on finitely many hyperplanes `⟪x, v⟫ = 0`
  (the vectors `v` of the simple roots are nonzero and orthogonal to
  `𝔞_G`), which are null sets, so the integral is that of the smooth
  function `c_M` (Arthur 2005, Lemma 17.1).
- Lapid's `T ∈ C` enters his proof only through the positive orthogonal set
  `Y(T)`: (15) gives `α(Y_Q(T)) ≥ c‖T‖`, and `Y_Q(T)` is affine in `T`, so
  `‖Y_Q(T)‖ ≤ κ(1 + c‖T‖)` for some `κ`. With `t = c‖T‖` the statement gives
  Lapid's bound, since `(1 + c‖T‖)^{-n}` is at most a constant times
  `(1 + ‖T‖)^{-n}`. A continuous seminorm on the Schwartz space is bounded by
  a constant times a finite supremum of the seminorms
  `schwartzSeminormFamily`, so Lapid's `μ_n` corresponds to
  `C · s.sup schwartzSeminormFamily`. The statement is thus the form of
  Lemma 8 that its proof gives for an arbitrary positive orthogonal set; its
  provenance is derived.
- The statement is uniform over all chambers `S₀`, since the values `d_S(0)`
  of a `(G, M)`-family coincide.
- If `t` stays bounded the inequality only says that the integral is bounded
  by Schwartz seminorms of the `d S`, which holds because `c_M` depends
  continuously on the family (Lapid's Corollary 3) and the functions
  `e^{λ(Y_P)}` and their derivatives are bounded polynomially in `‖Y_P‖`.
