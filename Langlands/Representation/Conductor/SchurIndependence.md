# Linear independence of the dominant Schur expressions

This internal unit proves that the integral-weight Schur expressions
`torusSchur K lam` (published in `Conductor/SphericalPolynomial`) of the dominant
weights are linearly independent over any field `K`. A weight
`lam : Fin (n + 1) → ℤ` is dominant when it is antitone,
`lam 0 ≥ lam 1 ≥ … ≥ lam n`. The planned uniqueness proof for Jacquet 2012,
Theorem 1 uses this fact. There, the vanishing of every Laurent coefficient of the
corank-one integral, expanded in spherical Whittaker values, should force every
dominant torus value of the Whittaker function to vanish. The result is the
linear-independence half of the classical fact that the Schur polynomials form a
basis of the symmetric polynomials; the spanning half is not proved here. It is
stated for the Library's integral-weight expression and proved directly, so it has
internal provenance.

## Definition

- `alternantExponent α : Fin (n + 1) → ℕ` sends `i` to `(α i - i + n).toNat`. These
  are the exponents in row `i` of the Library's `alternantMatrix R α`, whose
  `(i, k)` entry is `X k ^ (α i - i + n).toNat`. For a nonnegative `α` this is
  `α + δ` with `δ i = n - i`.

## Results

- `alternantExponent_strictAnti`: for an antitone `α` with nonnegative entries, the
  exponent tuple is strictly antitone.
- `alternantExponent_injective`: on nonnegative weights, `α ↦ alternantExponent α`
  is injective.
- `perm_eq_one_of_strictAnti_comp`: if `f ∘ σ = g` for strictly antitone
  `f g : Fin m → ℕ` and a permutation `σ`, then `σ = 1`. The proof shows that `σ` is
  strictly monotone, so it is the identity (`StrictMono.eq_id`).
- `prod_X_pow_eq_monomial`: `∏ i, X i ^ k i` is the monomial with exponent `k` and
  coefficient `1`.
- `coeff_det_alternantMatrix`: let `α` and `β` be antitone with nonnegative
  entries. The coefficient of the monomial with exponent `alternantExponent β` in
  `det (alternantMatrix R α)` is `1` if `α = β` and `0` otherwise. The proof expands
  the determinant by `Matrix.det_apply`. The term of `σ` is
  `sign σ • x^(alternantExponent α ∘ σ)`. It contributes to that coefficient only
  if `alternantExponent α ∘ σ = alternantExponent β`. Strict antitonicity forces
  `σ = 1`, and injectivity then forces `α = β`.
- `torusSchur_mul_determinantUnit_pow`: let `lam` be antitone and let `N : ℕ`
  satisfy `0 ≤ lam (last) + N`. Then `torusSchur K lam` times the `N`-th power of the
  coordinate-product unit is the image of the polynomial
  `jacobiTrudi K (lam + N)`. The proof writes `lam + N` as
  `(lam - lam (last)) + c` with `c = lam (last) + N`. It then applies the Library's
  `jacobiTrudi_add_nat` and combines the powers of the determinant unit.
- `torusSchur_linearIndependent`: the family `lam ↦ torusSchur K lam`, indexed by
  the antitone weights, is linearly independent over `K` in
  `TorusPolynomialAlgebra (Fin (n + 1)) K`.
- `symmetricTorusSchur_linearIndependent`: the same family is linearly independent
  in `symmetricTorusSubalgebra (Fin (n + 1)) K`. This follows from the previous
  result through the subalgebra inclusion.

## Proof of independence

Suppose `∑_{μ ∈ s} g μ • torusSchur K μ = 0` for a finite set `s` of antitone
weights. Choose `N` as the sum over `s` of `max(0, -μ (last))`, so that every
`μ + N` with `μ ∈ s` is nonnegative. Multiply the relation by the `N`-th power of the
coordinate-product unit and use `torusSchur_mul_determinantUnit_pow`. Injectivity of
the localization map (`torusPolynomialAlgebraMap_injective`) gives the polynomial
relation `∑ g μ • jacobiTrudi K (μ + N) = 0`. Multiplying by the base alternant
`det (alternantMatrix K 0)` and applying `jacobiTrudi_mul_baseAlternant` gives
`∑ g μ • det (alternantMatrix K (μ + N)) = 0`. Take the coefficient of the monomial
with exponent `alternantExponent (i + N)` for a fixed `i ∈ s`. By
`coeff_det_alternantMatrix` only the term `μ = i` survives, so `g i = 0`.
