# Euler characteristics of Künneth-type cohomology

Lean module: `Langlands.AlgebraicGeometry.Modules.KunnethEulerProduct`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`.

Author: Worker 998.

## Role and provenance

This is internal infrastructure for task `981f6bcb-41de-4a08-83b8-48b6eec2b236`, which proves
`Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement`. That proof needs
`χ(A ×_K A, m^*L ⊗ p^*M) = χ(L) χ(M)`, obtained from the shear automorphism and the
Library's Künneth theorem `Langlands.AlgebraicGeometry.Modules.coherentFieldExternalTensorKunneth`.
This module isolates the arithmetic step: a degreewise Künneth decomposition of cohomology
gives multiplicativity of the Euler characteristic. It is the elementary identity
`Σ_n (-1)^n Σ_{a+b=n} h^a h'^b = (Σ_a (-1)^a h^a)(Σ_b (-1)^b h'^b)` used, for example, in
Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), proof of (9.11), formulas (11)–(12),
printed p.132 (PDF p.136). All declarations are derived; none is a new statement target.

## Conventions

`relativeCohomology f n` is the Library's actual right-derived `K`-module cohomology along
`f : X ⟶ Spec K`, `HasFiniteCohomology f M` says that every `Hⁿ` is finite dimensional and
`Hⁿ = 0` for large `n`, and `eulerCharacteristic f M h` is the finite alternating sum of
dimensions.

## Declarations

- `kunnethIndexFintype n`: the index set `{(a, b) : ℕ × ℕ | a + b = n}` of the Künneth
  decomposition as a finite type, through `Finset.antidiagonal n`.
- `kunnethSum A B n`: the `K`-module `⨁_{a + b = n} A_a ⊗_K B_b`. This is the right-hand side
  of `CoherentFieldExternalTensorKunnethStatement`, written for arbitrary families.
- `finrank_kunnethSum`: if every `A_a` and `B_b` is finite dimensional, then
  `dim (kunnethSum A B n) = Σ_{(a,b) ∈ antidiagonal n} dim A_a · dim B_b`. Proof:
  `Module.finrank_directSum` for the finite index type, `Finset.sum_subtype` to pass to the
  antidiagonal, and `Module.finrank_tensorProduct`.
- `isZero_of_finrank_eq_zero`: a finite-dimensional module of dimension zero is a zero object.
- `alternatingDimensionPolynomial A N = Σ_{a < N} (-1)^a dim A_a · X^a ∈ ℤ[X]`, with
  `coeff_alternatingDimensionPolynomial` (its `a`-th coefficient is `(-1)^a dim A_a` when
  `dim A_a = 0` for `a ≥ N`), `natDegree_alternatingDimensionPolynomial_le` (degree at most `N`)
  and `eval_one_alternatingDimensionPolynomial` (its value at `1` is the truncated alternating
  sum).
- `hasFiniteCohomology_of_kunnethIso`: let `L` on `X` and `M` on `Y` have finite cohomology
  over `K`, and suppose `Hⁿ(Z, Q) ≅ ⨁_{a+b=n} Hᵃ(X, L) ⊗_K Hᵇ(Y, M)` for every `n`. Then `Q`
  has finite cohomology. Each `Hⁿ(Z, Q)` is finite dimensional because the direct sum is
  isomorphic to a finite product (`DirectSum.linearEquivFunOnFintype`) of finite-dimensional
  tensor products. If `Hᵃ(L) = 0` for `a ≥ N_L` and `Hᵇ(M) = 0` for `b ≥ N_M`, then for
  `n ≥ N_L + N_M` every summand has a zero factor, so `dim Hⁿ(Q) = 0` and `Hⁿ(Q)` is zero.
- `eulerCharacteristic_eq_mul_of_kunnethIso`: under the same isomorphisms, for any finite
  cohomology proof of `Q`, `χ(Q) = χ(L) · χ(M)`. Proof: let `P` and `R` be the alternating
  dimension polynomials of `L` and `M`, truncated at their vanishing bounds. By
  `Polynomial.coeff_mul` and `finrank_kunnethSum`, the `n`-th coefficient of `P R` is
  `(-1)^n dim Hⁿ(Q)`. The Library cutoff formula `eulerCharacteristic_eq_sum_range` writes all
  three Euler characteristics as finite sums. `Polynomial.eval_eq_sum_range'`, applied to
  `P R` with a bound above its degree, gives `χ(Q) = (P R)(1) = P(1) R(1) = χ(L) χ(M)`.

All proofs use only Mathlib and the published Library module
`Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof`.
