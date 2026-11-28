# Unimodularity of the general linear group of a non-archimedean local field

## Algebraic lemmas

- `map_diagonalUnits_mulSingle_eq_of_commGroup`: a homomorphism `ψ` from
  `GL_n(E)` to a commutative group takes the same value on the diagonal
  matrices with a single entry `a` in slot `i` or in slot `j`. A
  permutation matrix conjugates one into the other, and conjugation is
  invisible in a commutative target.
- `map_torus_of_commGroup`: such a homomorphism takes the diagonal matrix
  `diag(a ^ lam j)` to `ψ (diag(1, …, a, …, 1)) ^ (∑ j, lam j)`.
- `torus_const_commute`: the scalar matrix `a` is central.

The first two lemmas restate, as public declarations, the private
lemmas `map_diagonal_mulSingle_eq` and `map_torus` of
`Langlands.BaseChange.UnramifiedDeterminant`, with the same proofs.

## Over a non-archimedean local field

- `map_mul_right_eq_modularCharacter_smul`: for a Haar measure `μ` on
  `GL_n(E)`, the right translate `μ.map (· * g)` is
  `Measure.modularCharacterFun g • μ`. This is Mathlib's description of
  the modular character through `Measure.isMulLeftInvariant_eq_smul`, for
  the second-countable locally compact group `GL_n(E)`.
- `modularCharacterFun_generalLinear`: the modular character of `GL_n(E)`
  is trivial. Write `Δ` for the modular character. For `n = 0` the group
  is trivial, so `g = 1` and `Δ g = 1`. For `n > 0` the proof has three
  steps.
  1. `Δ` is trivial on the compact open subgroup `GL_n(𝒪)`: right
     translation by its elements preserves the subgroup, which has finite
     positive measure.
  2. `Δ` is trivial on the scalar uniformizer matrix `ϖ`. It is central
     (`torus_const_commute`), so right translation by it is a left
     translation, which preserves `μ`. By `map_torus_of_commGroup`, this
     gives `Δ (diag(ϖ, 1, …, 1)) ^ n = 1`, so
     `Δ (diag(ϖ, 1, …, 1)) = 1` in `ℝ≥0`. Hence `Δ` is trivial on every
     diagonal power matrix `diag(ϖ ^ lam j)`.
  3. Write `g = k₁ · diag(ϖ ^ lam j) · k₂` by the Cartan decomposition
     `Cartan.exists_cartan`, which gives `Δ g = 1`.
- `generalLinear_isMulRightInvariant`: every Haar measure on `GL_n(E)` is
  right invariant.

Unimodularity of reductive `p`-adic groups is standard; for `GL_n` it
follows from the Cartan decomposition as above. The module uses it to
form right-invariant Haar measures on standard Levi subgroups as products
of Haar measures on the blocks.
