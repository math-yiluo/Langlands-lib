# Proof of `RealLeftPolynomialGrowthStatement`

Module `Langlands.Representation.Archimedean.RealLeftPolynomialGrowthProof`, namespace
`Langlands.Archimedean`.

`realLeftPolynomialGrowth : RealLeftPolynomialGrowthStatement` proves the Library statement of
module `RealLeftPolynomialGrowth`. Let `ds` be a list of real blocks, `p + 1 < n`, `k : ℕ`, and
`Y` a subspace of the `O(n)`-finite functions of `realStandardModule n ds` whose elements are
polynomials of degree `< k` along every `t ↦ e(t) g`, with `e(t) = lowerRootElement n p hp t`.
Then the operators `h ↦ u h` from `Y`, `u ∈ U_d`, span a space of dimension at most
`C (d + 1)^(n (n - 1) - 1)`.

## Proof

It is the case `c₀ = (p + 1, p)` of `RootPolynomial.finrank_map_le_of_isRootPoly` (module
`RealRootPolynomialGrowth`).

1. The position `c₀ = (p + 1, p)` lies below the diagonal, since `p < p + 1`.
2. `lowerRootElement n p hp t = RootPolynomial.rootUnit _ t`. Both have matrix
   `1 + t E_{p+1,p}`: `lowerRootMatrix n p hp` is `Matrix.single ⟨p + 1, hp⟩ ⟨p, _⟩ 1`, which is
   `RootPolynomial.rootMatrix c₀`. They agree by `Units.ext rfl`.
3. For `h ∈ Y` and `g`, the hypothesis gives `q` of degree `< k` with `h(e(t) g) = q(t)`.
   Rewritten with step 2, this is the hypothesis of `RootPolynomial.isRootPoly_of_polynomial`,
   so `IsRootPoly _ k h`.
4. `RootPolynomial.finrank_map_le_of_isRootPoly ds _ k Y` then gives the constant `C`
   (`(n + 2)^N k` with `N = n (n - 1) / 2`) and the bound for every `d`.

The supporting modules are `RealSmoothRightAction`, `RealLowerUnipotentRestriction`,
`RealLeftPolynomialCount` and `RealRootPolynomialGrowth`. Their Markdown files explain the
argument. Evaluation at `1` is an eigenfunctional of the upper triangular Borel subalgebra that
is also killed by `E^k` on these functions. The value of `u h` at `n̄ ∈ N̄` then depends only on
`Ad(n̄) u` modulo a right ideal `J`. Two counts finish the proof: `U_d` modulo `J` has dimension at
most `k (d + 1)^(N - 1)`, and `v ↦ Ad(n̄(v)) u` is polynomial of degree at most `(1 + n) d` in
the `N` coordinates of `N̄`. A principal-series function vanishing on `N̄` is zero.
