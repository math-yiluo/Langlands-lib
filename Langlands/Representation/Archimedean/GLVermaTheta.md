# A trace functional on `Hom(W, M⁻(λ))`

Module `Langlands.Representation.Archimedean.GLVermaTheta`, namespace
`Langlands.Archimedean.GLReynolds`. It imports `GLTensorLowest` and `LowerVermaPBW` (the
ordered monomial basis `VermaPBW.basisU` of `U(𝔤𝔩_n(ℂ))`, the subalgebras
`VermaPBW.nUp n` (strictly upper triangular matrices `𝔫⁺`) and `VermaPBW.bLo n` (lower
triangular matrices including the diagonal, `𝔟⁻`), and the character `VermaPBW.muLo n λ` of
`𝔟⁻`, `Y ↦ Σ_p λ_p Y_pp`).

This module is part of a planned proof of Kostant's multiplicity bound
(`VermaGL.KostantMultiplicityStatement`, Library module `LowerVerma`). It contains no Library
statement and proves only the results listed below; no new axioms are used.

`M⁻(λ) = VermaGL.LowerVerma n λ` is the Library's lower Verma module
`U(𝔤𝔩_n) / U(𝔤𝔩_n)·{E_pq (q < p), E_pp - λ_p}` with generator `gen = [1]` and action
`VermaGL.action n λ` (Library `LowerVerma`).

## Results

### Functionals killing the raising operators

Let `h` be a family on `Y` satisfying the relations (`IsGlFamily`) and `Λ : Y → Z` a linear
map with `Λ(h_pq y) = 0` for all `p < q` and all `y`.

* `map_cas_of_upper`: for a weight vector `y` of weight `μ`,
  `Λ(c y) = casVal μ · Λ(y)`, with `c = Σ_{p,q} h_pq h_qp` the Casimir operator. The terms are
  computed one at a time. For `p < q`, `Λ(h_pq h_qp y) = 0`. For `p = q`, the term is
  `μ_p² Λ(y)`. For `q < p`, the relation `h_pq h_qp = h_qp h_pq + h_pp - h_qq` gives
  `(μ_p - μ_q) Λ(y)`.
* `map_aeval_cas_of_upper`: for any polynomial `Q`,
  `Λ(Q(c) y) = Q(casVal μ) · Λ(y)`. This follows by induction on powers, since `c^k y` is again a
  weight vector of weight `μ`.

### The map `Θ`

Fix a Lie algebra representation `σ` of `𝔤𝔩_n(ℂ)` on `W` and `λ : Fin n → ℂ`.

* `sigU σ`: the extension of `σ|𝔫⁺` to `U(𝔫⁺)`. `chiL λ`: the character of `U(𝔟⁻)`
  extending `muLo n λ`.
* `thetaU σ λ : U(𝔤𝔩_n) → End W`: the linear map that sends the ordered monomial
  `E^α = E^{α⁺} E^{α⁻}` (upper part, then lower part; `VermaPBW.basisU`) to
  `χ_λ(E^{α⁻}) σ(E^{α⁺})` (`thetaVal`, `Basis.constr`).
* `thetaU_mono`, `thetaU_subInc_mul`: `Θ(u⁺ u⁻) = χ_λ(u⁻) σ(u⁺)` for all `u⁺ ∈ U(𝔫⁺)` and
  `u⁻ ∈ U(𝔟⁻)` (images in `U(𝔤𝔩_n)`). This holds on monomials and extends by linearity in each
  factor (`VermaPBW.span_monoUp`, `VermaPBW.span_monoLo`).
* `thetaU_ι_mul`: `Θ(X u) = σ(X) Θ(u)` for `X ∈ 𝔫⁺`. `thetaU_mul_ι`:
  `Θ(u Y) = μ_λ(Y) Θ(u)` for `Y ∈ 𝔟⁻`. Both are checked on the basis `E^α`, where they reduce
  to `thetaU_subInc_mul` because `X E^{α⁺}` stays in `U(𝔫⁺)` and `E^{α⁻} Y` in `U(𝔟⁻)`.
* `thetaU_mul_mem`: `Θ(u x) = 0` for every `x` in the defining left ideal
  `VermaGL.lowerVermaIdeal n λ` and every `u`. By span induction it suffices to treat the
  generators. For `E_pq` with `q < p` the character value is `0`. For `E_pp - λ_p` the two
  terms cancel.
* `thetaU_one`: `Θ(1) = 1`.
* `theta σ λ : M⁻(λ) → End W`: the induced linear map on the quotient. `theta_mk`,
  `theta_gen` (`Θ(gen) = 1`), and `theta_action`: `Θ(X · m) = σ(X) Θ(m)` for `X ∈ 𝔫⁺`.
* `single_mem_nUp`: `E_pq ∈ 𝔫⁺` for `p < q`.

`Θ` generalizes the scalar functional `Psi` of `LowerVermaPBW`, which corresponds to the
one-dimensional case.

### The trace functional

* `lamFun σ λ : Hom(W, M⁻(λ)) → W^*`, `Λ(y)(w) = tr(w' ↦ Θ(y(w')) w)`.
* `lamFun_smulRight_gen` (`W` finite-dimensional): `Λ(ξ ⊗ gen) = ξ`, because
  `w' ↦ Θ(ξ(w') gen) w = ξ(w') w` has trace `ξ(w)` (`LinearMap.trace_smulRight`).
* `lamFun_homFam`: `Λ` kills `e_pq y` for `p < q`, where `e = homFam (famOf σ) (famOf action)`
  is the family on `Hom(W, M⁻(λ))` (`GLTensorLowest`). By `theta_action`, the operator
  `w' ↦ Θ((e_pq y)(w')) w` equals `σ(E_pq) G - G σ(E_pq)` with `G = (w' ↦ Θ(y(w')) w)`. Its
  trace is zero (`LinearMap.trace_mul_comm`).
* `lamFun_aeval_cas`: hence for `y` of weight `μ`,
  `Λ(Q(c) y) = Q(casVal μ) · Λ(y)` (`map_aeval_cas_of_upper`).

These are derived constructions written for this proof of Kostant's bound: `Λ` detects the
`ξ ⊗ gen`-component of a vector of `W^* ⊗ M⁻(λ)` modulo `𝔫⁺`, in the spirit of the
Harish-Chandra projection.
