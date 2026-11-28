# Central characters of mirror Verma modules across a wall

Module `Langlands.Algebra.HarishChandra.VermaWallCrossing`, namespace
`Langlands.Algebra.HarishChandra`.

## The data

`WallCrossing X X' α e f h` records two elements `X, X'` of `𝔥` and a root `α` (a linear form)
with `Re α(X) > 0 > Re α(X')`, such that every other root `χ ≠ ±α` has `Re χ(X) > 0` exactly
when `Re χ(X') > 0`. It also records `e ∈ 𝔤_α`, `f ∈ 𝔤_{-α}` and `h ∈ 𝔥` with `[e, f] = h` and
`α(h) = 2`. `WallCrossing.symm` gives the same data seen from `X'`, with `-α` and the triple
`f, e, -h`.

## The `𝔰𝔩₂` computations

- `pow_mul_ι_cartan`: `f^k h' = h' f^k + k α(h') f^k` in `U(𝔤)`, for `h' ∈ 𝔥`.
- `pow_succ_mul_ι_e`: `f^{k+1} e = e f^{k+1} - (k+1) f^k h + (k+1) k f^k`.
- `commonPositiveSubmodule X X'`: the sum of the weight spaces positive at both `X` and `X'`.
  `positiveRootSubmodule_le` and `positiveRootSubmodule_le'`: the positive roots at `X` are those
  of the common part together with `α`, and at `X'` together with `-α`. `lie_f_mem`: `ad f`
  preserves the common part. For a common positive root `χ`, `χ - α` is positive at `X'`. It
  differs from `±α`, by reducedness of the root system and because `χ ≠ 0`, so it is also
  positive at `X`. `pow_mul_mem`: hence `f^k x v` lies in the right ideal of the common part
  for `x` in it.

## Singular vectors

For a linear form `λ` with `λ(h) = -m`, `m ∈ ℕ`:

- `pow_succ_mul_mem_vermaIdeal`: `f^{m+1}` multiplies `R_X(λ + (m+1)α)` into `R_X(λ)`. On `e`
  this uses `f^{m+1} e ≡ -(m+1)(λ(h) + m) f^m = 0` modulo `R_X(λ)`.
- `pow_mul_mem_sup`: `f^m` multiplies `R_{X'}(λ + mα)` into `R_X(λ) + f^{m+1} U(𝔤)`, for every
  `λ`.
- `pow_not_mem_vermaIdeal`: no power of `f` lies in `R_X(λ)`. In a sorted basis for `X`, `f` is
  a nonzero multiple of a basis vector of negative real weight (`exists_eq_smul`,
  `orderedPBWMonomial_single`), and `not_mem_basisVermaIdeal` applies.
- `pow_not_mem_sup`: `f^m ∉ R_X(λ) + f^{m+1} U(𝔤)`. Otherwise `exists_eq_mul_of_mem_sup` gives
  `f^m = f^{m+1} y` with `y` in the span of the monomials in negative letters. The coefficient
  of the monomial `f^m` on the right vanishes: a monomial of `y` would have weight `α`, but
  monomials in negative letters have real weight `≤ 0` at `X`.

## The identity

- `eq_of_sub_mem_shift` and `eq_of_sub_mem_cross` compare scalars through these singular
  vectors with `eq_of_sub_mem_of_mul_sub_mem`.
- `sub_mem_vermaIdeal_of_eq_neg_nat`: for central `z` and `λ(h) = -m`, `z ≡ s` modulo `R_X(λ)`
  implies `z ≡ s` modulo `R_{X'}(λ - α)`. The cross comparison passes to `R_{X'}(λ + mα)`, and
  the shift comparison for the symmetric data, with `(λ + mα)(-h) = -m`, passes on to
  `R_{X'}(λ - α)`.
- `sub_mem_vermaIdeal`: the same for every `λ`. Both scalars are polynomial along the line
  `λ + t α/2` (`exists_polynomial_sub_mem_vermaIdeal`). They agree at the infinitely many `t`
  with `λ(h) + t ∈ -ℕ`, hence everywhere (`Polynomial.eq_of_infinite_eval_eq`).
