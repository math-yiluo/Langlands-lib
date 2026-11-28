# Integral matrices over a valued division ring are conjugate to integer matrices

The module `Langlands.LinearAlgebra.DivisionMatrixIntegerConjugation` proves that a square matrix
over a valued division ring which is integral in a suitable sense is conjugate, by an invertible
matrix, to a matrix all of whose entries have value at most one. It is used by
`Langlands.HarmonicAnalysis.UnitConjugation.ConjugationDomainProof` for the matrix factors
`M_d(D)` of a semisimple algebra over a local field, with `D` a possibly noncommutative
finite-dimensional division algebra.

## Setting

`D` is a division ring, possibly noncommutative, with a valuation `v : Valuation D Γ₀` into a
linearly ordered commutative group with zero (Mathlib's multiplicative convention:
`v (x * y) = v x * v y`, `v (x + y) ≤ max (v x) (v y)`). Vectors are row vectors
`Fin n → D`; a matrix `W` acts on the right by `x ᵥ* W` (`Matrix.vecMul`), which is left
`D`-linear in `x`.

## Declarations

- `rowSpan v W`, for `W : Matrix (Fin m) (Fin n) D`: the set of left combinations `x ᵥ* W` of
  the rows of `W` with coefficients `x i` of value at most one. It contains every row
  (`row_mem_rowSpan`) and `0`, and is closed under addition, under left multiplication by
  elements of value at most one and under finite sums (`zero_mem_rowSpan`, `add_mem_rowSpan`,
  `smul_mem_rowSpan`, `sum_mem_rowSpan`).
- `exists_rowSpan_eq_of_relation`: if the rows of `W : Matrix (Fin (m + 1)) (Fin n) D` satisfy a
  relation `a ᵥ* W = 0` with `a ≠ 0`, some `W' : Matrix (Fin m) (Fin n) D` has
  `rowSpan v W' = rowSpan v W`.
- `exists_units_conj_integral`: let `W₀` be any matrix with `n` columns such that
  `L = rowSpan v W₀` contains the standard row vectors `Pi.single k 1` and satisfies
  `y ᵥ* Y ∈ L` for all `y ∈ L`. Then there is a unit `u` of `Matrix (Fin n) (Fin n) D` with
  `v ((u * Y * u⁻¹) i j) ≤ 1` for all `i j`. The hypothesis on the standard row vectors cannot
  be dropped: the set `{0}`, the span of the empty family of rows, is stable under every `Y`,
  while the `1 × 1` matrix `Y = [1/2]` over `ℚ₂` with the `2`-adic valuation is conjugate only to
  itself and its entry has value `2`. When `W₀` consists of the rows of `Y ^ 0, …, Y ^ (r - 1)`,
  the hypothesis holds exactly because `r > 0` makes the rows of `Y ^ 0 = 1` available.
- `exists_units_conj_integral_of_aeval`: let `D` be an algebra over a field `F`, and let
  `p : F[X]` be monic with `v (algebraMap F D (p.coeff i)) ≤ 1` for all `i` and
  `aeval Y p = 0`. Then the conclusion of `exists_units_conj_integral` holds for `Y`.

## Proofs

`exists_rowSpan_eq_of_relation`. Choose an index `i₀` at which `v (a i)` is largest; then
`a i₀ ≠ 0`. The vector `b = (a i₀)⁻¹ • a` has `b i₀ = 1`, all `v (b i) ≤ 1` and `b ᵥ* W = 0`.
Let `W'` be `W` with row `i₀` removed (rows `W (i₀.succAbove j)`). A combination of the rows of
`W'` is the combination of the rows of `W` with coefficient `0` at `i₀` (`Fin.insertNth`).
Conversely, `x ᵥ* W = (x - x i₀ • b) ᵥ* W`; the new coefficients have value at most one by the
ultrametric inequality and vanish at `i₀`, so this is a combination of the rows of `W'`
(`Fin.sum_univ_succAbove`).

`exists_units_conj_integral`. Among all matrices `W` with `rowSpan v W = L`, take one with the
least number `m` of rows (`Nat.find`). Its rows are left linearly independent: otherwise
`exists_rowSpan_eq_of_relation` produces a generating matrix with `m - 1` rows. Since each
`Pi.single k 1` lies in `L`, there is `X : Matrix (Fin n) (Fin m) D` with `X * W = 1`. Since each
row `W i` lies in `L`, so does `W i ᵥ* Y`, which gives `C : Matrix (Fin m) (Fin m) D` with
entries of value at most one and `W * Y = C * W`. Every row of `W * X - 1` is killed by `W`,
because `(W * X - 1) * W = W * (X * W) - W = 0`, so independence gives `W * X = 1`. Thus
`x ↦ x ᵥ* W` is a left `D`-linear equivalence `(Fin m → D) ≃ (Fin n → D)` with inverse
`y ↦ y ᵥ* X`, and comparing `Module.finrank` gives `m = n`. The unit `u = ⟨W, X⟩` satisfies
`u * Y * u⁻¹ = W * Y * X = C * W * X = C`.

`exists_units_conj_integral_of_aeval`. Let `r = p.natDegree`. If `r = 0`, the constant monic
annihilator is `p = 1`, so `aeval Y p = 1 = 0` and the matrix ring is trivial: every matrix is
`0` and `u = 1` works. Otherwise `r > 0`; take for `W₀` the
matrix whose rows are the rows `(Y ^ i) k` for `i < r` and `k : Fin n`, indexed through
`finProdFinEquiv`. The rows of `Y ^ 0 = 1` are the standard row vectors. Right multiplication
by `Y` sends the row `(Y ^ i) k` to `(Y ^ (i + 1)) k`; for `i + 1 < r` this is a row of `W₀`, and
for `i + 1 = r` the relation `Y ^ r = -∑_{j < r} p_j • Y ^ j` (from `Polynomial.Monic.as_sum`)
writes it as a combination of rows of `W₀` with coefficients `-algebraMap F D p_j` of value at
most one. Hence right multiplication by `Y` preserves `rowSpan v W₀`, and
`exists_units_conj_integral` applies.

## Provenance

This is an internal lemma. Its conclusion is the classical fact that an integral element of
`M_n(D)` over a local field lies in a conjugate of the maximal order `M_n(O_D)`; the classical
proof chooses a basis of a `Y`-stable `O_D`-lattice. The proof here replaces the structure theory
of `O_D`-lattices by the minimal generating family argument above, which uses only the
ultrametric valuation on `D`.
