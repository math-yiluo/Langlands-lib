# Strict Jacquet exponent bounds for square-integrable product-Levi representations

Author: Worker 246.

This module is a helper for the proof of
`Langlands.GLProductLeviSquareIntegrableLpStatement` in
[`ProductLeviSquareIntegrableLpProof`](ProductLeviSquareIntegrableLpProof.md).
Its declarations are in the namespace `Langlands.ProductLeviSquareIntegrable`.
It proves the strict exponent bound that square integrability modulo the centre
imposes on the generalized eigencharacters of the normalized refined Jacquet
modules of a representation of an actual GL block Levi. No published statement
is proved here.

## Main results

- `norm_lt_one_of_diagonal`. Let `M = C.Levi F.Carrier` carry
  `T.leviTopologicalGroup C`, and let `μ` be a Borel Haar measure on
  `M ⧸ Subgroup.center M`. Let `σ` satisfy `IsSquareIntegrableModCenter σ μ`.
  Let `ψ` be a generalized eigencharacter of the pullback of
  `T.normalizedRefinedJacquet C D σ` through `flattenedLeviEquiv` and the
  flattened `blockScalarLevi`. This is the same pullback as in
  `GLProductLeviTemperedExponentNecessityStatement`. Let `c` be a weakly
  contracting nested tuple whose `j`-th block scalar is the diagonal matrix with
  `T.uniformizer` on a set `S` and `1` elsewhere. Assume that `S` and `Sᶜ` are
  nonempty and that the refined modulus of `c` is `q ^ (-|S| |Sᶜ|)`. Then
  `‖ψ (flatScalars C D c)‖ < 1`. The inequality is strict. The tempered
  analogue `ProductLeviNecessity.norm_le_one_of_diagonal` only gives `≤ 1`.
- `StrictFundHypothesis T C ρ` is a `Prop`-valued abbreviation. It says that
  for every fundamental index `s : FundIndex C` and every generalized
  eigencharacter `ψ` of the pulled-back normalized refined Jacquet module for
  `fundRefinement C s`, we have
  `‖ψ (flatScalars C (fundRefinement C s) (fundScalars T C s))‖ < 1`. These are
  the refinements `(k, C.size j - k)` and the scalars `(ϖ, 1)` of
  `ProductLeviChamberBoundProof`.
- `strictFundHypothesis_of_squareIntegrable`: if
  `IsSquareIntegrableModCenter σ μ`, then `StrictFundHypothesis T C σ`.
  Irreducibility is not used.

## Disjointness of the cells of different powers

`pow_eq_of_mk_eq` is the new geometric input. Let the `j`-th block of `g` be
`d = diag(ϖ on S, 1 elsewhere)`, and let `S` and `Sᶜ` be nonempty. Suppose
`mulSingle j (unip S Y) * g ^ M * k` and
`mulSingle j (unip S Y') * g ^ M' * k'` have the same image modulo the centre,
with `k j, k' j ∈ GL(O)`. Then `M = M'`. The proof works in block `j`. Let `s`
be the central quotient of the two block components, with scalar `c`, and put
`κ = k_j k'_j⁻¹ ∈ GL(O)`. Then

```text
d^(-M) unip(Y' - Y) d^(M') = κ s,   κ⁻¹ = s · d^(-M') unip(Y - Y') d^M.
```

The diagonal entries of `D₁ · unip · D₂` with `D₁, D₂` diagonal are the products
of the diagonal entries (`diagonal_unip_diagonal_apply_self`).
`val_inv_of_val_eq_diagonal` computes the inverse of a diagonal unit. Take
`b ∉ S` and `a ∈ S`. The `b`-entries give `1 = κ_bb c` and `(κ⁻¹)_bb = c`.
Integrality of `κ` and `κ⁻¹` then gives `v(c) = 1`. The `a`-entries give
`ϖ^(M' - M) = κ_aa c` and `(κ⁻¹)_aa = c ϖ^(M - M')`. Hence both
`exp (M - M')` and `exp (M' - M)` are at most `1`
(`valuation_uniformizerUnit_inv_pow_mul_pow`), so `M = M'`.

## Summed cell lower bound

`sum_mul_le_lintegral` generalizes the published
`ProductLeviNecessity.card_mul_le_lintegral` to different lower bounds `a i` on
the disjoint translates. `cells_sum_lower_bound` has the same hypotheses as the
published `ProductLeviNecessity.cells_lower_bound`, together with nonempty `S`
and `Sᶜ`. It gives `t` such that for every `L`

```text
∑_{m < L} q ^ (m |S| |Sᶜ|) · F0 (m + t) · μ(mk '' KP) ≤ ∫⁻ f ∂μ.
```

The translating elements are indexed by pairs `(m, δ)` with `m < L` and
`δ : Pairs S → Fin m → ResidueField`. They are
`mulSingle j (unip S (ϖ ^ t · digitVal δ)) * g ^ (m + t)`. Translates of
different `m` are disjoint by `pow_eq_of_mk_eq`. Translates of the same `m` are
disjoint by the published `level_of_mk_eq` and `eq_of_level_digitVal_sub`.

## Proof of `norm_lt_one_of_diagonal`

The published `exists_eigen_coefficient` (module `ProductLeviNecessityEigen`),
applied with the integral Levi as neighbourhood, gives a compact open `K`, a
`K`-fixed vector `x` and a `K`-invariant smooth functional `ℓ` with `ℓ x ≠ 0`
and `ℓ(σ(g ^ m) x) = λ ^ m ℓ x`. Here
`λ = compressionEigenvalue = √δ(c) ψ(c)`. So the coefficient equals
`λ ^ M ℓ x` on `u g ^ M k` for `u, k ∈ K`. Let `f = ‖coefficientNorm ℓ x‖ₑ ^ 2`.
Its integral is finite by the `L²` hypothesis
(`lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`). Suppose
`‖ψ(c)‖ ≥ 1`. Since `δ(c) = q ^ (-P)` with `P = |S| |Sᶜ|`, we get
`q ^ P ‖λ‖ ^ 2 = ‖ψ(c)‖ ^ 2 ≥ 1`. Then every summand of
`cells_sum_lower_bound` is at least `C0 = ‖λ‖ₑ ^ (2t) ‖ℓ x‖ₑ ^ 2 μ(mk '' K)`.
This number is positive, because `mk '' K` is open, and the summand is
`(q ^ P ‖λ‖ₑ ^ 2) ^ m C0`. So `L · C0 ≤ ∫⁻ f` for every `L`. Since `C0 > 0` and
the integral is finite, this is impossible (`ENNReal.exists_nat_gt`).

## Proof of `strictFundHypothesis_of_squareIntegrable`

`fundScalars_eq_testScalars` identifies `fundScalars T C s` with the published
test tuple `testScalars T C (fundRefinement C s) s.1 1 1` of
`ProductLeviNecessityCombinatorics`. The published lemmas of
`ProductLeviNecessityTest` give weak contraction, the diagonal block scalar on
`testSet` and the refined modulus `q ^ (-|S| |Sᶜ|)`. Compare this modulus with
`fund_refinedLeviModulus`, which gives `q ^ (-(k (N - k)))` with
`0 < k < N`. Since `q > 1`, `zpow_right_inj₀` gives `|S| |Sᶜ| = k (N - k) > 0`.
So `S` and `Sᶜ` are nonempty, and `norm_lt_one_of_diagonal` applies.

## Provenance

This is the strict half of Casselman's square-integrability criterion
(Casselman 1995, `casselman-1995-admissible-representations`, Theorem 4.4.6;
Waldspurger 2003, `waldspurger-2003-plancherel`, Proposition III.1.1, printed
p.263). There, square integrability makes every exponent lie in the open
positive cone. Only the evaluation at the fundamental coweights is formalized
here, because that is what the strict chamber bound uses. The Lean argument
follows neither source. It sums explicit lower bounds for the coefficients of
compression eigenvectors over disjoint unipotent translates of the cells of all
powers, extending the tempered necessity argument of `ProductLeviNecessityCells`.
