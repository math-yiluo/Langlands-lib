# Galois descent of semilinear vector spaces and Hilbert 90 for matrices

This internal linear algebra module is derived from standard Galois descent
for vector spaces (Speiser's lemma) and its matrix form, Hilbert's Theorem 90
for `GL_n`. Mathlib's `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`
covers only `GL_1` (the unit group of the field), and the published
`GaloisLineDescent` module covers only one-dimensional spaces; this module
supplies the case of arbitrary dimension.

The setting is fields `k` and `L` in one universe, an algebra `k → L`, and a
subgroup `H` of the actual `k`-algebra automorphisms of `L`. The fields may have
any characteristic. The extension `L/k` is not assumed finite or Galois; only
`H` is assumed finite, so for example `H` may be `Gal(M/L')` sitting inside the
automorphism group of `M` over a smaller base. The vector space `V` lies in an
independent universe and need not be finite-dimensional. The matrix index type
`n` lies in a third universe and is finite with decidable equality.

## Statements

- `coeff_eq_zero_of_sum_eq_zero` (Dedekind independence): if `H` is a
  `Fintype` and `g : H → L` satisfies `∑_σ g(σ) σ(a) = 0` for every `a : L`,
  then every `g(σ)` is zero.
- `span_fixed_eq_top`: let `f : H → V →+ V` be an additive action that is
  semilinear, meaning `f 1 = id`, `f (σ τ) = f σ ∘ f τ` and
  `f σ (a • v) = σ(a) • f σ v`. Then the vectors fixed by every `f σ` span `V`
  over `L`.
- `exists_fixed_basis`: under the same hypotheses, `V` has an `L`-basis,
  indexed by a set of vectors, all of whose members are fixed by every `f σ`.
- `exists_matrix_coboundary` (Hilbert 90 for `GL_n`): let
  `c : H → Matrix n n L` satisfy `c 1 = 1` and the cocycle law
  `c (σ τ) = c σ * σ(c τ)`, where `σ(-)` applies `σ` to every entry. Then
  there is `P : GL n L` with `c σ * σ(P) = P` for every `σ`.
- `eq_mul_map_inv_of_mul_map_eq`: for one automorphism `σ` of `L` over `k`
  and `P : GL n L`, the equation `c * σ(P) = P` implies `c = P * σ(P⁻¹)`.
- `exists_matrix_coboundary'`: hence the same `P` gives the coboundary form
  `c σ = P * σ(P⁻¹)` for every `σ`.
- `coboundaryMatrix` (the selected definition): the noncomputable choice, by
  `Classical.choose`, of a matrix `P : GL n L` as in
  `exists_matrix_coboundary`, for a given matrix cocycle together with proofs
  of its two laws. It is not canonical: any `P` multiplied on the right by an
  invertible matrix over the fixed field of `H` also works.
  `coboundaryMatrix_spec` records `c σ * σ(P) = P` and
  `eq_coboundaryMatrix_mul` records `c σ = P * σ(P⁻¹)` for this choice.

The cocycle is a matrix-valued function; invertibility of its values is not
assumed, since it follows from the conclusion.

## Proofs

Dedekind independence is Mathlib's `linearIndependent_toLinearMap`, applied to
the injective family of `k`-algebra maps underlying the elements of `H`.

For `span_fixed_eq_top`, suppose the span of the fixed vectors were a proper
subspace. `Submodule.exists_le_ker_of_lt_top` gives a nonzero `L`-linear
functional `φ` vanishing on it. For every vector `w`, the trace
`∑_τ f τ w` is fixed, because left multiplication by `σ` permutes `H`.
Applying this to `w = a • v` and using semilinearity gives
`∑_τ φ(f τ v) τ(a) = 0` for all `a`. Dedekind independence then makes every
coefficient zero; the coefficient at `τ = 1` is `φ(v)`. Hence `φ = 0`, a
contradiction.

`exists_fixed_basis` extracts a linearly independent subset of the fixed
vectors with the same span (`exists_linearIndependent`) and turns it into a
basis by the previous theorem.

For `exists_matrix_coboundary`, the cocycle defines the semilinear action
`f σ v = c σ * σ(v)` on column vectors `n → L`; the identity and cocycle laws
give the action laws, and entrywise application of `σ` gives semilinearity.
A fixed basis is reindexed by `n` (both bases of `n → L` have the same
cardinality), and `P` is the matrix whose `j`-th column is the `j`-th fixed
basis vector, invertible because it is a change-of-basis matrix. Fixedness of
each column is exactly `c σ * σ(P) = P`. For the primed form,
`eq_mul_map_inv_of_mul_map_eq` multiplies this equation on the right by
`σ(P⁻¹)`, using that applying `σ` entrywise is multiplicative and
`σ(P) σ(P⁻¹) = σ(1) = 1`. The two lemmas about `coboundaryMatrix` are the
choice specification and its consequence by the same lemma.

## Scope

This module supplies no group scheme, descent of schemes, or Hermitian form. It
is a linear algebra prerequisite for trivialising Galois cocycles with values in
`GL_n`, as needed when a projective Galois discrepancy has been normalised to an
honest matrix cocycle.
