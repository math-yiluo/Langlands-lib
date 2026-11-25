# Submodules of the dual unramified principal series orthogonal to the spherical vector

Lean module: `Langlands.Representation.Archimedean.RealSphericalInduction`, namespace
`Langlands.Archimedean.RealSphericalInduction`. It imports `RealSphericalLimit` and
`JacquetKernel`, and it is part of the proof of `RealSphericalCyclicStatement`.

## Auxiliary lemmas

- `dualChar_dualChar`: `dualChar (dualChar χ) = χ`.
- `re_le_of_le`: if `IsWeaklyDominant e m` and `j ≤ k ≤ m`, then `Re e_k ≤ Re e_j`.
- `isWeaklyDominant_shift`: if `IsWeaklyDominant e m`, then the shifted exponents
  `e_l − 1/2` are weakly dominant for `m − 1`.
- `sub_sub_one_ne_zero`: if `IsWeaklyDominant e m` and `j < m`, then `e_m − e_j − 1 ≠ 0`. Its
  real part is `≤ −1`.
- `spherical_of_mem`: the spherical vector `signVector n e 0 0` equals `1` on `O(n)`.

## Main result `eq_bot`

Let `n ∈ ℕ`. Let `χ` be a signed power with exponents `e`, with `χ_l(−1) = 1` for every `l`,
and with `IsWeaklyDominant e (n − 1)`. Let `U` be a subspace of the `O(n)`-finite functions of
the principal series of `dualChar χ` on `GL_n(ℝ)`. Assume that `U` is stable under right
translation by `O(n)` and under all right derivatives, and that `∫_{O(n)} u = 0` for every
`u ∈ U`. Then `U = 0`.

Proof by recursion on `n`, along the maximal parabolic subgroup `P_{n−1,1}`. The pattern is
`JacquetDual.jacquet_eq_zero`.

- `n = 0`. `GL_0(ℝ)` is trivial and `haarK 0` is a probability measure, so
  `∫ u = u(1) = 0`, that is, `u = 0`.
- `n = m + 1`.
  1. Let `A = JacquetKernel.annihilator (dualChar χ) U` be the set of `O(m+1)`-finite `h` in
     the principal series of `χ` (by `dualChar_dualChar`) with `∫_{O(m+1)} h u = 0` for all
     `u ∈ U`. It is stable under right derivatives (`annihilator_rightDerivative`).
  2. The spherical vector `T₀` lies in the principal series (`signVector_mem` with trivial
     signs). It lies in `A` because `∫ T₀ u = ∫ u = 0`.
  3. By `RealSphericalReach.regularized_mem` and `sub_sub_one_ne_zero`, the regularized
     vector `H = signVector (m+1) e 0 (bump 0 m 1)` lies in `A`. So `∫ u H = 0` for every
     `u ∈ U`.
  4. Orthogonality invariance (`JacquetDual.integral_mul_eq_zero_of_orthogonal`, which uses
     the `O(m+1)`- and Lie-stability of `U`) upgrades this to
     `∫_{O(m+1)} u(κ g) H(κ) dκ = 0` for every `g`.
  5. `RealSphericalLimit.integral_iota_eq_zero` gives `∫_{O(m)} u(ι(k)) dk = 0` for every
     `u ∈ U`.
  6. The restriction `U ∘ ι` (`JacquetDual.restrictLevi`) is a subspace of the
     `O(m)`-finite principal series of `dualChar (shiftChar χ)` on `GL_m(ℝ)`
     (`restrictLevi_mem`). It is `O(m)`-stable (`rightTranslation_restrictLevi`) and stable
     under right derivatives (`rightDerivative_restrictLevi`). The shifted character
     `shiftChar χ` is a signed power with exponents `e_l − 1/2`, trivial signs
     (`shiftChar_neg_one`) and weakly dominant exponents (`isWeaklyDominant_shift`).
     By step 5, every function of `U ∘ ι` has integral `0` over `O(m)`.
  7. The recursion for `m` gives `U ∘ ι = 0`. Since `U` is `O(m+1)`-stable,
     `JacquetDual.map_restrictLevi_ne_bot` shows `U = 0`.

## Provenance

The module was written for this project. It adapts the induction `D(n)` of the Library's
`JacquetDual` (strict Langlands lemma) to the closed chamber. In place of the
Jacquet integral of an arbitrary vector, the spherical vector is replaced by its regularized
multiple `H`, which lies in the same `(𝔤, K)`-annihilator (`RealSphericalReach`). The
statement is the dual form of Kostant's cyclicity of the spherical vector, as quoted by
N. Wallach, *Cyclic vectors and irreducibility for principal series representations*,
Trans. Amer. Math. Soc. 158 (1971), Theorem 3.1. The proof here does not follow Kostant's or
Wallach's argument.
