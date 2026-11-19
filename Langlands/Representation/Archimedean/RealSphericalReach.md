# The regularized spherical vector lies in the Lie span of the spherical vector

Lean module: `Langlands.Representation.Archimedean.RealSphericalReach`, namespace
`Langlands.Archimedean.RealSphericalReach`. It imports `RealSphericalStep` and
`JacquetNonvanishing`, and it is part of the proof of `RealSphericalCyclicStatement`.

Setting: `χ : ℕ → ℝˣ → ℂ` is a signed power with exponents `e` (`IsSignedPower χ e`).
`principalSeries ℝ N χ` is the Library's principal series, and `signVector N e p a` is the
function of `JacquetNonvanishing` that restricts to `κ ↦ ∏_l κ_{ll}^{p_l + 2 a_l}` on `O(N)`.
The spherical vector is `T₀ = signVector N e 0 0`, which equals `1` on `O(N)`
(`spherical_of_mem`).

## Exponent equivariance

- `apply_exp`: `χ_l(e^x) = exp(e_l x)`.
- `isExpEquivariant_of_mem`: every element of the principal series of `χ` is
  `IsExpEquivariant` for `α_i = e_i + (N − 1)/2 − i`. This applies the Library's
  `isExpEquivariant_of_mem_principalSeries`.

## Reachable quadratic functions

`quad p c b κ = ∑_l p_l κ_{lc} κ_{lb}` comes from `RealSphericalStep`. It is additive and
homogeneous in `p` (`quad_zero`, `quad_add`, `quad_smul`). For a subspace `A` of functions
on `GL_N(ℝ)` and an index `b`, `reach A b` is the set of `p ∈ ℂ^N` for which there are
`G_0, …, G_{N−1} ∈ A` with `G_c = quad p c b` on `O(N)`. It is a subspace of `ℂ^N`.

`sVec N e l = (e_l + (N − 1)/2 − l) + l`, the diagonal `α_l + l` of the operator in the step
formula.

- `sOp_mem_reach`. Let `A` consist of `O(N)`-finite functions of the principal series of
  `χ` and be stable under all right derivatives. Then `reach A b` is stable under
  `sOp (sVec N e)`. Given witnesses `G_c` for `p`, the functions
  `G'_a = ∑_c R(E_{ac}) G_c` lie in `A`. By `RealSphericalStep.sum_rightDerivative_single` they
  satisfy `G'_a = quad (S p) a b` on `O(N)`.
- `one_mem_reach`. If `T₀ ∈ A`, the all-ones vector lies in `reach A b`. Take
  `G_b = T₀` and `G_c = 0` for `c ≠ b`. The columns of `κ` are orthonormal (`sum_col_mul`),
  so `quad 1 c b κ = δ_{cb}`.

## The main lemma `regularized_mem`

Let `m ∈ ℕ`, and let `χ` be a signed power with exponents `e` and `χ_l(−1) = 1` for every `l`.
Let `A` be a subspace of the `O(m+1)`-finite functions of the principal series of `χ` on
`GL_{m+1}(ℝ)`. Suppose `A` is stable under all right derivatives and contains `T₀`, and
`e_m − e_j − 1 ≠ 0` for every `j < m`. Then `A` contains
`H = signVector (m+1) e 0 (bump 0 m 1)`, the function of the principal series that
restricts to `κ ↦ κ_{mm}²` on `O(m+1)`.

Proof.

1. `sVec(m) − sVec(j) − 1 = e_m − e_j − 1 ≠ 0` for `j < m`.
2. `RealSphericalKrylov.single_last_mem` applies with `Z = reach A m`, `P = 1`, stability
   from `sOp_mem_reach` and `1 ∈ Z` from `one_mem_reach`. It gives that the last basis
   vector `δ_m` lies in `reach A m`.
3. Let `G_c` be the witnesses. Then `G_m ∈ A` and `G_m(κ) = κ_{mm}²` on `O(m+1)`.
4. `H` is in the principal series (`signVector_mem` with `p = 0`, which uses `χ_l(−1) = 1`),
   and `H(κ) = κ_{mm}²` on `O(m+1)`. Two functions of the principal series that agree on
   `O(m+1)` are equal (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`). So `G_m = H ∈ A`.

## Provenance

The module was written for this project. The vector `H` is the "regularized" spherical
vector. It is `qFun · T₀` (`JacquetNonvanishing.signVector_bump`), and its partial Jacquet
integral along `P_{m,1}` converges in the closed chamber, where the one of `T₀` may not. The
condition `e_m − e_j − 1 ≠ 0` holds whenever the real parts of the `e_l` weakly decrease.
