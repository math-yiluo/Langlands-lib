# Recovering summands from weighted power sums

Module `Langlands.Analysis.SeveralComplex.PowerSumInterpolation`, namespace
`Langlands.Analysis.SeveralComplex`.

`K` is a field, `F` a `K`-vector space and `Λ` an arbitrary index type.

## Definition

`powerSumVector k S m c : Fin k → F` for `k : ℕ`, a finite set `S : Finset K`, weights
`m : K → K` and `c : K → F` is the vector of weighted power sums

`powerSumVector k S m c j = ∑_{u ∈ S} m(u) • (u^j • c(u))`, `j = 0, …, k - 1`.

## Results

- `sum_coeff_smul_powerSumVector`: for a polynomial `P` with `natDegree P < k`,
  `∑_{j < k} P.coeff j • powerSumVector k S m c j = ∑_{u ∈ S} m(u) • (P(u) • c(u))`.
- `mem_span_of_powerSumVector_mem_span` (**summands from power sums**). Assume
  `card S ≤ k` and that for every `l : Λ` the vector `powerSumVector k S m (c l)` lies in the
  `K`-span of `{powerSumVector k S m (c μ) | μ ∈ s₀}` for a set `s₀ ⊆ Λ`. Then for every
  `u₀ ∈ S` with `m(u₀) ≠ 0` and every `l`, the vector `c l u₀` lies in the span of
  `{c μ u₀ | μ ∈ s₀}`.

## Proofs

- The first identity exchanges the two finite sums and uses
  `P(u) = ∑_{j < k} P.coeff j · u^j` (`Polynomial.eval_eq_sum_range'`, valid since
  `natDegree P < k`).
- For the main result let `P = Lagrange.basis S id u₀`, the Lagrange basis polynomial with
  `P(u₀) = 1` and `P(u) = 0` for the other `u ∈ S` (`Lagrange.eval_basis_self`,
  `Lagrange.eval_basis_of_ne`); its degree is `card S - 1 < k`
  (`Lagrange.natDegree_basis`). The linear map
  `L y = m(u₀)⁻¹ • ∑_{j < k} P.coeff j • y j` then sends `powerSumVector k S m (c μ)` to
  `c μ u₀` for every `μ`, by the first identity. Applying `L` to the hypothesis
  (`Submodule.mem_map_of_mem`, `Submodule.map_span`) gives the claim.

## Provenance

Internal. Elementary linear algebra (Lagrange interpolation; equivalently, invertibility of a
Vandermonde matrix with distinct nodes), formulated as needed for the dimension reduction in the
proof of `Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`.
There `S` is the set of zeros of a holomorphic function on a disc, `m` their multiplicities and
`k` the total number of zeros (module `ZeroCounting`).
