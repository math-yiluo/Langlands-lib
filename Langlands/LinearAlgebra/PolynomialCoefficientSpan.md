# Coefficients and values of vector-valued polynomials

This is a derived linear-algebra construction. Let `k` be a field, `σ` any
variable type, and `V` a `k`-vector space. A polynomial with vector coefficients
is represented by a finitely supported function
`P : (σ →₀ ℕ) →₀ V`. The multi-index `d` records its monomial, and `P d` is its
coefficient. Neither `σ` nor `V` needs to be finite or finite-dimensional.

`Langlands.LinearAlgebra.PolynomialCoefficients.evaluation t` is the linear map
sending `P` to

`∑ d ∈ P.support, (∏ i ∈ d.support, t i ^ d i) • P d`.

The products and sum are the finitely supported operations; in particular the
zero multi-index contributes its coefficient unchanged. `evaluation_apply`
gives this formula, and `map_evaluation` proves that applying any linear map to
the result is the same as applying it to every coefficient before evaluation.
For a scalar functional `f`, `scalarPolynomial f P` packages those coefficients
as an ordinary `MvPolynomial σ k`; `scalarPolynomial_coeff` and
`eval_scalarPolynomial` identify its coefficients and evaluations.

Assume now that `k` is infinite. For every submodule `S` of `V`,
`evaluation_mem_iff_coefficient_mem` proves

`(∀ t : σ → k, evaluation t P ∈ S) ↔ (∀ d : σ →₀ ℕ, P d ∈ S)`.

The difficult direction is `coefficient_mem_of_evaluation_mem`. Take any scalar
functional in the dual annihilator of `S`. It vanishes on every evaluation of
`P`, so `eval_scalarPolynomial` and Mathlib's scalar multivariate polynomial
extensionality make the entire scalar polynomial zero. Extracting its
coefficient gives `f (P d) = 0`. Mathlib's dual-annihilator separation criterion
then gives `P d ∈ S`. This uses algebraic duals and has no topological or
finite-dimensional hypothesis. Conversely,
`evaluation_mem_of_coefficient_mem` uses closure of a submodule under scalar
multiplication and finite sums; that direction does not require infinitude.

`span_range_evaluation_eq_span_range_coefficients` applies these two membership
directions to the respective spans. It shows that all values of `P` span exactly
the same subspace as all its coefficients, including coefficients outside the
support, which are zero. In any possibly noncommutative `k`-algebra `A` with a
ring structure, `adjoin_range_evaluation_eq_adjoin_range_coefficients` then shows
that the values and coefficients generate the same unital `k`-subalgebra. Its
proof applies algebraic adjoining to the span equality and uses
`Algebra.adjoin_span`.

For coefficients in `V →ₗ[k] W`, `evaluation_apply_linearMap` proves that
applying the evaluated map to `v` equals evaluating the polynomial with
coefficients `(P d) v`. The proof specializes `map_evaluation` to the linear
map of application at `v`. Consequently,
`mapsTo_evaluation_iff_mapsTo_coefficients` says that every value maps a
submodule `S` into a submodule `T` exactly when every coefficient does. Its two
directions apply the coefficient/value membership lemmas to each fixed `v ∈ S`.
Specializing `W = V` and `T = S` gives
`invariant_evaluation_iff_invariant_coefficients`: polynomial endomorphism
values and their coefficient operators preserve precisely the same subspaces.
The adjoining equality also applies directly to this endomorphism algebra.

The provenance is the elementary argument above, implemented using Mathlib's
finite sums, scalar polynomial extensionality, dual separation and adjoining
operations. No external literature theorem is assumed. This supplies a general
coefficient-recovery prerequisite for future polynomial root-action arguments.
It constructs no root action, divided-power identification, highest-weight
module or general Steinberg module, and does not prove
`Langlands.GroupScheme.SteinbergBigCellStatement`.
