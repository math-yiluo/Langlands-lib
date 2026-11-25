# Multiplicity one of minor-monomial `U(n)`-types in complex principal series

Lean module: `Langlands.Representation.Archimedean.ComplexLowestKTypeMultOne`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It is also a supporting lemma for the proof of the
Library statement `ComplexTemperedStandardIrreducibleStatement` (written U below) in
`ComplexTemperedStandardIrreducibleProof`, which imports it. The statement
`ComplexTemperedCyclicVectorStatement` (module
`ComplexTemperedComplement`, proved there as `complexTemperedCyclicVector`) derives
irreducibility from a cyclic vector `f₀` that every `U(n)`-equivariant endomorphism maps to a
multiple of itself. This module supplies the second hypothesis for every vector whose
restriction to `U(n)` is a minor monomial. The cyclicity of such a vector is shown in
`ComplexTemperedStandardIrreducibleProof`, through the product lemma `complexMinorProductCyclic`
(module `ComplexMinorProductCyclic`).

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ` and `U(n)` is `Matrix.unitaryGroup (Fin n) ℂ`
(as a subgroup of `GL_n(ℂ)`: `unitaryCompact ℂ n`, with `Unitary.toUnits`). For characters
`χ : ℕ → ℂˣ → ℂ`, `X(χ)` is the space of `U(n)`-finite functions of `principalSeries ℂ n χ`
(`kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)`, abbreviated `KX n χ`), and
`ρ = principalSeriesRep ℂ n χ` is right translation by `U(n)` on it:
`(ρ(k) f)(g) = f(g k)`. For a list `ds` of complex characters, `complexStandardModule n ds` is
`principalSeries ℂ n (complexPositionCharacter ds)` and `complexStandardRep n ds` is the
corresponding `ρ`. Unprefixed names are in `Langlands.Archimedean.ComplexLowestKType`.

## Definitions

All matrices are `n × n` complex matrices, indexed by `Fin n`.

* `botIdx j`, `topIdx j` (`j : Fin n`): the increasing maps `Fin (j + 1) → Fin n` onto the last
  `j + 1` indices `n − (j + 1), …, n − 1` and onto the first `j + 1` indices `0, …, j`.
* `minor j g = Δ_{j+1}(g)`: the determinant of the submatrix of `g` on the rows `botIdx j` (the
  bottom `j + 1` rows) and the columns `topIdx j` (the first `j + 1` columns).
* `lowMinor j g`: the determinant of the submatrix of `g` on the bottom `j + 1` rows and the last
  `j + 1` columns.
* `minorMonomial c d g = det(g)^d ∏_{j<n} Δ_{j+1}(g)^{c_j}` for `c : Fin n → ℕ`, `d : ℤ`
  (integer power; `det g ≠ 0` for the unitary `g` where it is used).
* `lowMonomial c d g = det(g)^d ∏_{j<n} lowMinor j g ^ {c_j}`.
* `wt i = n − 1 − i` and `torus s = D_s = diag(s^{n−1}, …, s, 1)`.
* `bot j`: the set of the bottom `j + 1` indices; `lowExp j = e_j = ∑_{i ∈ bot j} wt i`;
  `totExp c = ∑_j e_j c_j`.
* `coef A C j S`: for a `(j + 1)`-element set `S` of indices, the product of the minor of `A` on
  the rows `botIdx j` and the columns `S`, and the minor of `C` on the rows `S` and the columns
  `topIdx j` (both in increasing order).
* `redPoly A C j = ∑_S coef A C j S · X^{σ(S) − e_j}` with `σ(S) = ∑_{i ∈ S} wt i`, and
  `prodPoly c A C = ∏_j (redPoly A C j)^{c_j}`; polynomials over `ℂ`.
* `wgt c d s = det(D_s)^d s^{totExp c}`.
* `torusUnit s hs`, `torusU s hs` (for `‖s‖ = 1`): the diagonal entries `s^{wt i}` as units, and
  `D_s` as the element `ComplexPrincipalSeriesExtension.phaseMatrix (torusUnit s hs)` of `U(n)`;
  `coe_torusU` shows that its matrix is `torus s`.
* `torusChar χ s hs`: `principalSeriesCharacter ℂ n χ` at the phases of `torusUnit s hs`, the
  scalar by which every function of the principal series transforms under left multiplication
  by `D_s` (`apply_torusU_mul`).
* `avg χ N ζ hζ w κ f = ∑_{t<N} (w t)⁻¹ • ρ(D_{ζ^t}) (ρ(κ) f) ∈ X(χ)`, for `f ∈ X(χ)`,
  `κ ∈ U(n)`, `ζ` with `‖ζ^t‖ = 1` for all `t` and weights `w : ℕ → ℂ`.
* `KX n χ`: abbreviation of the `U(n)`-finite functions of `principalSeries ℂ n χ`.

## The statement

`Langlands.Archimedean.ComplexLowestKTypeMultOneStatement`: for every `n`, every list `ds` of
complex characters, every `c : Fin n → ℕ` and `d : ℤ`, and every `U(n)`-finite function `f₀` of
`complexStandardModule n ds` with `f₀(κ) = det(κ)^d ∏_{j<n} Δ_{j+1}(κ)^{c_j}` for all `κ ∈ U(n)`,
every `ℂ`-linear endomorphism `E` of the `U(n)`-finite functions of `complexStandardModule n ds`
commuting with `complexStandardRep n ds k` for all `k ∈ U(n)` satisfies `E f₀ = a • f₀` for some
`a ∈ ℂ`.

No condition on `ds` (length, exponents) is assumed; if no such `f₀` exists, or `f₀ = 0`, the
statement is trivially true for it.

It is proved as `Langlands.Archimedean.complexLowestKTypeMultOne`, from the general version
`exists_smul_of_minorMonomial` for the principal series of any `χ : ℕ → ℂˣ → ℂ`.

Provenance. Derived, internal infrastructure for the proof of U along the route of
`ComplexTemperedStandardIrreducibleProof` (a
cyclic lowest-`U(n)`-type vector whose `U(n)`-type has multiplicity one). Only the form above, for
minor-monomial vectors and endomorphisms commuting with `U(n)`, is stated and proved; no
literature statement is claimed.

## Corollary

`Langlands.Archimedean.complexTemperedIrreducible_of_minorMonomial`: let `ds` be a list of `n`
complex characters whose exponents all have the same real part, and let `f₀ ≠ 0` be a
`U(n)`-finite function of `complexStandardModule n ds` whose restriction to `U(n)` is
`minorMonomial c d`. If every subspace of the `U(n)`-finite functions stable under
`complexStandardRep n ds` and `complexStandardLie n ds` that contains `f₀` is everything, then
`IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)`. Proof:
`complexTemperedCyclicVector` with the multiplicity-one hypothesis supplied by
`complexLowestKTypeMultOne`.

## Proof

### Algebra

* `minor_mul_torus_mul` (Cauchy–Binet): `Δ_{j+1}(A D_s C) = ∑_S coef A C j S · s^{σ(S)}`, the sum
  over the `(j + 1)`-element sets `S`. The submatrix of `A D_s C` is the product of the
  `(j + 1) × n` matrix (rows `botIdx j` of `A`) times `D_s` and the `n × (j + 1)` matrix
  (columns `topIdx j` of `C`). The Library's
  `Langlands.GeneralLinear.Spherical.det_rectangular_mul` expands it, and the minor of the rows
  of `A` times `D_s` on the columns `S` is the minor of `A` times `∏_{i ∈ S} s^{wt i}`.
* `exp_bound`: `e_j + |S \ bot j| ≤ σ(S)` for every `(j + 1)`-element `S`. The indices outside
  `bot j` have `wt i ≥ j + 1`, those of `bot j` missing from `S` have `wt i ≤ j`, and both sets
  have the same size.
* `minor_eq_eval`: `Δ_{j+1}(A D_s C) = s^{e_j} · (redPoly A C j)(s)`.
* `eval_zero_redPoly`: `(redPoly A C j)(0) = lowMinor j A · Δ_{j+1}(C)`. Only `S = bot j` has
  exponent `σ(S) − e_j = 0` (by `exp_bound`), and its coefficient is that product
  (`orderEmbOfFin_bot`).
* `natDegree_redPoly_le`, `natDegree_prodPoly_le`: `deg redPoly ≤ n²`,
  `deg prodPoly ≤ ∑_j c_j n²`. Also `eval_zero_prodPoly`.
* `minorMonomial_mul_torus_mul`:
  `M(A D_s C) = det(A)^d det(C)^d · wgt c d s · (prodPoly c A C)(s)` for `M = minorMonomial c d`.
* `minor_torus_mul`, `minorMonomial_torus_mul`: `Δ_{j+1}(D_s C) = s^{e_j} Δ_{j+1}(C)` and
  `M(D_s C) = wgt c d s · M(C)`; `D_s` scales the bottom rows.
* `sum_eval_rootsOfUnity`: for a primitive `N`-th root of unity `ζ` and `deg Q < N`,
  `∑_{t<N} Q(ζ^t) = N · Q₀` (geometric sums of `ζ^i ≠ 1`, `0 < i < N`, vanish).
* `wgt_ne_zero`, and `sum_minorMonomial`: for such `ζ` with `∑_j c_j n² < N`,
  `∑_{t<N} wgt(ζ^t)⁻¹ M(A D_{ζ^t} C) = N · lowMonomial c d A · M(C)`.

### Representation

* `apply_torusU_mul`: for `f` in the principal series, `f(D_s κ) = torusChar χ s hs · f(κ)`, by
  `ComplexPartialJacquet.phaseMatrix_toUnits` and the left equivariance of the principal series.
* `torusChar_eq`: if `f₀` is in the principal series, restricts to `M` on `U(n)`, and
  `f₀(κ₁) ≠ 0`, then `torusChar χ s hs = wgt c d s`: compare `f₀(D_s κ₁)` computed by
  `apply_torusU_mul` and by `minorMonomial_torus_mul`.
* `rep_rep_apply`, `avg_apply`: `(avg κ f)(x) = ∑_{t<N} (w t)⁻¹ f(x · D_{ζ^t} κ)`.
* `map_avg`: a `U(n)`-equivariant `E` commutes with `avg κ`.
* `exists_smul_of_minorMonomial`. If `f₀` vanishes on `U(n)` then `f₀ = 0`
  (`ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary`) and `a = 0` works. Otherwise fix `κ₁`
  with `f₀(κ₁) ≠ 0`. Take `N = ∑_j c_j n² + 1`, `ζ = exp(2πi/N)` (`Complex.isPrimitiveRoot_exp`;
  `‖ζ‖ = 1`), and `w t = wgt c d (ζ^t)`.
  1. For every `f ∈ X(χ)`: `(avg κ f)(1) = N f(κ)`, since `f(D_{ζ^t} κ) = w t · f(κ)` by
     `apply_torusU_mul` and `torusChar_eq`.
  2. For `k ∈ U(n)`: `(avg κ f₀)(k) = N · lowMonomial c d k · f₀(κ)`, by `sum_minorMonomial`
     with `A = k`, `C = κ`.
  3. Hence `avg κ f₀ = (f₀(κ)/f₀(κ₁)) • avg κ₁ f₀`: both are in the principal series and agree
     on `U(n)` by step 2 (`eq_of_eqOn_unitary`).
  4. Apply `E` (`map_avg`) and evaluate at `1` (step 1 for `E f₀`):
     `N (E f₀)(κ) = (f₀(κ)/f₀(κ₁)) · N (E f₀)(κ₁)`.
  5. So `E f₀` and `a • f₀` with `a = (E f₀)(κ₁)/f₀(κ₁)` agree on `U(n)`, hence are equal
     (`eq_of_eqOn_unitary`).
* `complexLowestKTypeMultOne` is `exists_smul_of_minorMonomial` for
  `χ = complexPositionCharacter ds`.
