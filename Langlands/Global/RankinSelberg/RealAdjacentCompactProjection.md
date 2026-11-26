# Finite compact projections of real Whittaker coefficients

Write `G = GL_(r+1)(ℝ)`, `O(r+1) = unitaryCompact ℝ (r+1)` for its orthogonal subgroup, `ι` for
the inverse transpose and `wd` for `ArchimedeanLocal.dualFunction (r+1)`, the dual
`V ↦ (g ↦ V(w₀ ι(g)))` with the long Weyl element `w₀`. The module turns a compact projection
formula for a uniform real Whittaker map into a finite separation of variables, and provides
the compact pairings that serve as the separated coefficients. The reduction is the real
counterpart of `complexLocalCompactProjectionReduction` in the Library's
`ComplexLocalCompactProjection`.

## Results

- `inverseTranspose_orthogonal`: `ι g = g` for `g ∈ O(r+1)`.

- `realLocalCompactProjectionReduction`, the proof of
  `RealLocalCompactProjectionReductionStatement r`. Let `K` be a compact topological group with
  Borel measurable structure and a Haar measure `μ`, and `iK : K → G` a continuous homomorphism
  whose image is exactly `O(r+1)`. Let `κ` be a continuous weight on `K` whose left translates
  `k ↦ κ(x⁻¹ k)` span a finite-dimensional space. Let `B` be a uniform real Whittaker map of
  character `a` on the compact-finite standard module of a block list `ds`
  (`IsRealUniformWhittakerIntertwiner r ds a B`), and `f` a vector of that module. Assume that
  for each `g ∈ G` a vector `p(g)` of the module satisfies
  `p(g)(iK x) = ∫_K κ(k) f(iK(x) iK(k) g) dμ(k)` for `x ∈ K`, and
  `B(p(g))(x) = ∫_K κ(k) B f(x iK(k) g) dμ(k)` for `x ∈ G`.
  Then there are `m`, functions `W_1, …, W_m` in `realUniformWhittakerModel r ds a` and
  continuous weights `κ'_1, …, κ'_m` on `K` such that for all `x, g ∈ G`
  `∫_K κ(k) B f(x iK(k) g) dμ(k) = Σ_j W_j(x) · ∫_K κ'_j(k) f(iK(k) g) dμ(k)` and
  `∫_K κ(k) wd(B f)(x iK(k) g) dμ(k) = Σ_j wd(W_j)(x) · ∫_K κ'_j(k) f(iK(k) ι(g)) dμ(k)`.

- `compactPairing r χ iK hiK μ w hw`: for a finite measure `μ` on `K` and a continuous weight
  `w`, the linear form `φ ↦ ∫_K w(k) φ(iK k) dμ(k)` on the smooth principal series
  `principalSeries ℝ (r+1) χ`. `compactPairing_apply` unfolds it.

- `hasCompactDerivativeBound_compactPairing`: if `iK` maps into `O(r+1)`, the compact pairing on
  the principal series of the position characters of `ds` has a compact derivative bound
  (`RealPrincipalSeries.HasCompactDerivativeBound`) with the single empty derivative word and the
  constant `∫_K ‖w‖ dμ`.

- `compactPairing_translate`: on the right translate by `g` of the included standard vector `f`
  (expanded to its position characters), the compact pairing is `∫_K w(k) f(iK(k) g) dμ(k)`.

## Proofs

For the reduction, restriction to `iK(K)` is an injective linear map from the standard module to
functions on `K`: two vectors of a principal series that agree on the orthogonal group are equal
(`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`), and every orthogonal matrix is some `iK k`.
The finite span of the left translates of `κ` gives a finite convolution kernel
(`ComplexJacquet.hasFiniteCompactConvolutionKernel_of_finite_translates`), and the Library's
`ComplexJacquet.exists_compactPairing_expansion`, which is stated for an arbitrary compact group,
writes each `p(g)` as a finite combination `Σ_j (∫_K κ'_j(k) f(iK(k) g) dμ(k)) v_j` of fixed
vectors `v_j` with continuous `κ'_j`. Applying `B` and the second hypothesis gives the first
expansion with `W_j = B v_j`, which lie in the uniform model. For the dual expansion, `ι` is
multiplicative and fixes every `iK k`, so `wd(B f)(x iK(k) g) = B f(w₀ ι(x) iK(k) ι(g))`; the first
expansion at `w₀ ι(x)` and `ι(g)` is the second one.

The derivative bound of a compact pairing uses only the values of a vector on `O(r+1)`, which
`HasCompactDerivativeBound` bounds through the empty derivative word: the norm of the integral is
at most `∫_K ‖w‖ dμ` times the supremum of the vector on `O(r+1)`.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, pp. 59–60: after substituting the reproducing
identity of an elementary idempotent `ξ`, Jacquet writes
`∫ W'(x k h) ξ(k) dk = Σ_i W'_i(x) f_i(h)` with `W'_i` in the Whittaker model and `f_i` matrix
coefficients. Here the compact projection formula for the Whittaker map is a hypothesis, the
weight is any continuous weight whose left translates span a finite-dimensional space, and the
coefficients are the explicit compact integrals `∫_K κ'_j(k) f(iK(k) g) dμ(k)`, which are matrix
coefficients of the principal series for the compact pairings of this module.
