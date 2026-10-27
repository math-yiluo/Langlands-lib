# Common eigenvectors and exponential bounds for powers of endomorphisms

Author: Worker 246.

This module collects finite-dimensional complex linear algebra used by the
product-Levi chamber bound. Everything is in the namespace
`Langlands.EndomorphismBound`. The definition `endNorm` is an internal size
function; it encodes no external mathematics.

## Common eigenvectors

`exists_common_eigenvector`: for any index type `ι` and any family
`f : ι → Module.End ℂ M` of pairwise commuting endomorphisms of a nontrivial
finite-dimensional complex space `M`, there is `v ≠ 0` such that for every `i`
some `c : ℂ` has `f i v = c • v`. The proof is strong induction on `finrank`
(`exists_common_eigenvector_aux`). If every `f i` is a scalar, any nonzero
vector works. Otherwise choose a non-scalar `f i` and one of its eigenvalues
(`Module.End.exists_eigenvalue`). The eigenspace is a proper, nonzero subspace
that every `f j` preserves, because the operators commute; restrict to it and
recurse. The pattern follows the published
`DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero`.

## Characters from eigenvectors

`exists_character_of_forall_eigen`: let `π` be a representation of a group `A`
on a complex space `X`, and let `w ≠ 0` be an eigenvector of every `π a`. Then
there is a character `χ : A →* ℂˣ` with `π a w = χ a • w` for all `a`. The
eigenvalue function is multiplicative because `w ≠ 0`, and `χ` is
`MonoidHom.toHomUnits` of it.

## The size function and power bounds

For a finite-dimensional complex space `W`, `endNorm f` is the `L¹–L∞`
operator norm, Mathlib's `Matrix.linftyOpNormedRing`, of the matrix of `f` in
`Module.finBasis ℂ W`. The matrix norm instances are local to this module.
Consumers use only the following properties.

- `endNorm_nonneg` and `endNorm_mul_le`: `endNorm (f * g) ≤ endNorm f * endNorm g`.
- `matrix_pow_bound`: if every element of the spectrum of a complex square
  matrix `X` has norm at most `r₀ ≥ 0`, then for every `r > r₀` there is `c`
  with `‖X ^ m‖ ≤ c * r ^ m` for all `m`. The proof uses Gelfand's formula, via
  Mathlib's `spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius`, in the
  complete normed algebra of matrices. The `limsup` of `‖X^m‖^(1/m)` is below
  `r`, so `‖X^m‖ ≤ r^m` for all large `m`. The finitely many remaining powers
  are absorbed in the constant.
- `exists_endNorm_pow_le`: suppose `f x = μ • x` with `x ≠ 0` implies
  `‖μ‖ ≤ r₀`. Then for every `r > r₀` some `c` has `endNorm (f ^ m) ≤ c * r ^ m`
  for every `m`. The matrix of `f` has the spectrum of `f`
  (`AlgEquiv.spectrum_eq`), and on a finite-dimensional space the spectrum
  consists of eigenvalues (`Module.End.hasEigenvalue_iff_mem_spectrum`).
- `exists_apply_le_endNorm`: for a fixed functional `φ` and vector `v`, there
  is `C ≥ 0` with `‖φ (f v)‖ ≤ C * endNorm f` for all `f`. The map
  `f ↦ φ (f v)` is linear on the finite-dimensional matrix space, hence
  bounded.
