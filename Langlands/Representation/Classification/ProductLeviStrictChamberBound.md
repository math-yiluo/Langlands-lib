# Strict chamber bound for square-integrable product-Levi coefficients

Author: Worker 246.

This module is a helper for the proof of
`Langlands.GLProductLeviSquareIntegrableLpStatement` in
[`ProductLeviSquareIntegrableLpProof`](ProductLeviSquareIntegrableLpProof.md).
Its declarations are in the namespace `Langlands.ProductLeviSquareIntegrable`.
It is the strict counterpart of the published chamber bound
`ProductLeviChamber.chamber_bound` of
[`ProductLeviChamberBoundProof`](ProductLeviChamberBoundProof.md) and of
`ProductLeviTempered.cell_coefficient_bound` of
[`ProductLeviTemperedSufficiencyProof`](ProductLeviTemperedSufficiencyProof.md).
The weak exponent hypothesis `UpperExponentHypothesis` is replaced by
`StrictFundHypothesis` of
[`ProductLeviSquareIntegrableExponent`](ProductLeviSquareIntegrableExponent.md).
No published statement is proved here.

## Main results

All results are for an admissible representation `ρ` of `C.Levi F.Carrier` on a
complex space `V`, with the topology `T.leviTopologicalGroup C`.

- `exists_character_of_eigenvalue`. Let `c` be a strictly contracting nested
  tuple, and let `K` be compact open subgroups with block Iwahori factorizations
  for `D`. Let `μ ≠ 0` be an eigenvalue of the compression by
  `fun i => (D i).blockScalar (c i)` on the vectors fixed by
  `leviPiOpenSubgroup T C K`. Then there is a character `χ` with open kernel that
  is a generalized eigencharacter of the pulled-back normalized refined Jacquet
  module, and

  ```text
  ‖μ‖ = √(refinedLeviModulus (flatScalars C D c)) · ‖χ (flatScalars C D c)‖.
  ```

- `fund_norm_eigenvalue_lt`. Under `StrictFundHypothesis T C ρ`, every eigenvalue
  of the compression by `leviRep T C (fundTuple C s)` satisfies
  `‖μ‖ < √(fundWeight T C s)`.
- `strict_chamber_bound`. Assume `StrictFundHypothesis T C ρ`, and let `U` be a
  neighbourhood of `1`. Then there is `ε > 0` with the following property. For
  every smooth functional `ℓ` and vector `v`, both fixed pointwise by `U`, there
  is `c` with

  ```text
  ‖ℓ(ρ(leviRep T C lam) v)‖ ≤ c · ∏ j, delta T (lam j) ^ (1/2 + ε)
  ```

  for all blockwise normalized `lam`.
- `strict_cell_coefficient_bound`. Assume `StrictFundHypothesis T C ρ`. Then for
  every `ℓ` and `v` there are `ε > 0` and `cb` such that the same bound, with
  `cb`, holds at `k₁ * leviRep T C lam * k₂` for all `k₁, k₂` in
  `ProductLeviTempered.integralLevi T C`.

## Proofs

`exists_character_of_eigenvalue` reuses the argument of the published
`ProductLeviChamber.norm_eigenvalue_le` without its final inequality. The
argument runs through the stable image, the bijectivity
`Jacquet.refinedStableImageJacquetBijective`, the eigenspace of the unnormalized
Jacquet action, a common eigenvector of the commuting normalized block-scalar
action (`EndomorphismBound.exists_common_eigenvector`), and the character
`exists_character_of_forall_eigen`. Openness of the kernel comes from
smoothness of the pulled-back normalized Jacquet module. The identity
`χ(c) = (√δ(c))⁻¹ μ` gives the norm equation.

`fund_norm_eigenvalue_lt` treats `μ = 0` directly, because
`√(fundWeight s) > 0`. Otherwise it rewrites the fundamental Levi element as the
block scalar of `fundScalars T C s` (`fundScalars_blockScalar`) and applies
`exists_character_of_eigenvalue` with the strictly contracting
`fundScalars_isStrictlyContracting`. It then uses the strict hypothesis
`‖χ(fundScalars)‖ < 1` and `fund_refinedLeviModulus`, `fundWeight_eq`.

`strict_chamber_bound`:

1. `CuspidalSupport.exists_leviPiOpenSubgroup_subset_forall` gives `K` with
   product `KP ⊆ U` and block Iwahori factorizations for every block shape. The
   space `W` of `KP`-fixed vectors is finite-dimensional, and `A(lam)` is the
   compression by `leviRep T C lam` on `W`.
2. Each `A(fundTuple s)` has finitely many eigenvalues
   (`Module.End.finite_hasEigenvalue`), and each has norm `< √(w_s)` with
   `w_s = fundWeight T C s`. The map `ε ↦ w_s ^ (1/2 + ε)` is continuous at `0`
   (`Real.continuousAt_const_rpow`), so for all `ε` near `0` every eigenvalue of
   every `A(fundTuple s)` has norm `< w_s ^ (1/2 + ε)`. The index set
   `FundIndex C` is finite. `Metric.eventually_nhds_iff` gives a radius `δ`. Put
   `ε₀ = δ / 2`. Then all eigenvalues have norm at most
   `r0_s = w_s ^ (1/2 + ε₀)`, and `r0_s < r_s = w_s ^ (1/2 + ε₀/2)` because
   `0 < w_s < 1`.
3. The rest is the published proof of `chamber_bound` with `r_s` in place of
   `w_s ^ (1/2 - η)`. `EndomorphismBound.exists_endNorm_pow_le` gives
   `endNorm (A(fundTuple s) ^ m) ≤ cs_s r_s ^ m`. Multiplicativity of
   compression along antitone tuples and the decomposition
   `lam = ∑ s, fundCoeff lam s • fundTuple s` bound `endNorm (A lam)`. Then
   `prod_delta_eq` turns `∏ s, r_s ^ fundCoeff lam s` into
   `∏ j, delta T (lam j) ^ (1/2 + ε₀/2)`. The exponent gap is `ε = ε₀ / 2`. It
   depends only on `U` through `KP`, not on `ℓ` or `v`.

`strict_cell_coefficient_bound` follows the published
`cell_coefficient_bound`. The orbits of `v` under `ρ` and of `ℓ` under the
smooth contragredient, restricted to the compact open `integralLevi`, are finite
(`Compact.finite_orbit_of_smooth`). The set `U` of elements fixing every vector
and every functional of these two finite orbits is a finite intersection of
neighbourhoods of `1` (`Filter.biInter_finset_mem`). So `strict_chamber_bound`
for this `U` gives one `ε` for all pairs of orbit elements. The coefficient at
`k₁ a k₂` is the coefficient of `(k₁⁻¹ · ℓ, ρ(k₂) v)` at `a`, and `cb` is the sum
of the absolute values of the constants over the pairs of orbit elements.

## Provenance

The strict decay `|f(a)| ≤ c δ(a) ^ (1/2) q ^ (-ε' σ(a))` on the positive chamber
is the estimate obtained in the proof of Waldspurger 2003
(`waldspurger-2003-plancherel`), Corollary III.1.2 (printed p.264), from the
open-cone condition on the exponents. The Lean bound `c ∏ δ ^ (1/2 + ε)` is an
estimate of the same kind: compared with the tempered size `δ ^ (1/2)` it has
the extra factor `∏ δ ^ ε`, which decays exponentially in the degree of the
exponent tuples. It is stated with `δ` rather than with Waldspurger's `σ`
because the cell volumes are bounded by `∏ δ⁻¹`. The Lean route does not use
Waldspurger's `Ξ`. It is the Casselman-style compression argument of
`ProductLeviChamberBoundProof`, with strict spectral bounds at the fundamental
coweights.
