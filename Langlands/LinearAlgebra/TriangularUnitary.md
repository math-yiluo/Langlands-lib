# Upper triangular times unitary factorization with entry bounds

This module works with square matrices indexed by `Fin n` over a field `𝕜` with
an `RCLike` structure (the real or complex numbers), for every `n : ℕ`, including
`n = 0`. Norms of entries are the `RCLike` absolute values, and `ᴴ` is the
conjugate transpose.

## Provenance

The content is derived and internal. These are the standard Cholesky and
triangular–unitary (`QR`-type) factorizations of linear algebra, with explicit
entry bounds, proved from Mathlib's `LDL` decomposition
(`Mathlib.Analysis.Matrix.LDL`). No original source is cited and none is
formalized. The module is a helper for the archimedean places of the adelic
`GL(n)` reduction: a matrix with bounded entries and bounded inverse entries
factors as a triangular matrix with bounded entries, bounded inverse entries and
diagonal bounded away from zero, times a unitary matrix.

## Definition

* `IsTriangularUnitaryFactorization g b u` is the proposition that `b` is upper
  triangular (`b i j = 0` for `j < i`), `b` is invertible, `u` lies in the
  unitary group `unitaryGroup (Fin n) 𝕜` (that is, `u * star u = 1` and
  `star u * u = 1`), and `g = b * u`.

## Results

* `isUpperTriangular_conjTranspose`: the conjugate transpose of a lower
  triangular matrix is upper triangular.
* `isUpperTriangular_mul_diagonal`: an upper triangular matrix times a diagonal
  matrix is upper triangular.
* `exists_upperTriangular_mul_conjTranspose` (upper Cholesky factorization):
  every positive definite `P` equals `b * bᴴ` for an invertible upper triangular
  `b`.
* `exists_upperTriangular_mul_unitary`: every invertible `g` has `b` and `u`
  with `IsTriangularUnitaryFactorization g b u`.
* `norm_sq_le_re_mul_conjTranspose_self`: `‖M i j‖ ^ 2` is at most the real part
  of `(M * Mᴴ) i i`.
* `re_mul_conjTranspose_self_le`: if every entry of `M` has norm at most `B`,
  the real part of `(M * Mᴴ) i i` is at most `n * B ^ 2`.
* `norm_le_one_of_mem_unitaryGroup`: every entry of a unitary matrix has norm at
  most `1`.
* `mul_unitary_mul_conjTranspose`: `(M * u) * (M * u)ᴴ = M * Mᴴ` for unitary `u`.
* `norm_mul_unitary_le`, `norm_unitary_mul_le`: if `0 ≤ B` bounds the entry norms
  of `M` and `u` is unitary, then `√n * B` bounds the entry norms of `M * u` and
  of `u * M`.
* `inv_apply_self_mul_apply_self`: for an invertible upper triangular `b`,
  `b⁻¹ i i * b i i = 1` for every `i`.
* `bounds_of_isTriangularUnitaryFactorization`: if
  `IsTriangularUnitaryFactorization g b u`, `0 ≤ B`, `0 ≤ B'`, every entry of `g`
  has norm at most `B` and every entry of `g⁻¹` has norm at most `B'`, then every
  entry of `b` has norm at most `√n * B`, every entry of `b⁻¹` has norm at most
  `√n * B'`, and every diagonal entry of `b` has norm at least `(√n * B')⁻¹`.

## Proofs

* Cholesky. `P⁻¹` is positive definite. Mathlib's `LDL.lowerInv` gives a lower
  triangular invertible `L` with `L * P⁻¹ * Lᴴ = D`, where `D` is the diagonal
  matrix of `LDL.diagEntries`. Since `D` is positive definite, its diagonal
  entries are positive reals `d i`. Put `s i = (√(d i))⁻¹` and
  `b = Lᴴ * diagonal s`. Then `b` is upper triangular, its determinant is a unit,
  and `diagonal s * (diagonal s)ᴴ = E`, the diagonal matrix of the `(d i)⁻¹`,
  with `E * D = 1`. From `E * D = 1` one obtains `Lᴴ * E * L * P⁻¹ = 1`, hence
  `Lᴴ * E * L = P`, which is `b * bᴴ = P`.
* Triangular times unitary. For invertible `g`, `g * gᴴ` is positive definite.
  Take its Cholesky factor `b` and put `u = b⁻¹ * g`. Then
  `u * uᴴ = b⁻¹ * (g * gᴴ) * (bᴴ)⁻¹ = 1`, and `g = b * u`.
* Entry bounds. The real part of `(M * Mᴴ) i i` is the sum of the `‖M i k‖ ^ 2`;
  this gives the first two bounds, and the unitary case where this sum is `1`.
  Right multiplication by a unitary matrix does not change `M * Mᴴ`, which gives
  the bound for `M * u`. The bound for `u * M` follows by applying it to `Mᴴ` and
  `uᴴ` and taking the conjugate transpose.
* Diagonal entries. The inverse of an invertible upper triangular matrix is upper
  triangular (Mathlib's `blockTriangular_inv_of_blockTriangular`), so the
  diagonal entry `(b⁻¹ * b) i i = 1` reduces to the single term
  `b⁻¹ i i * b i i`.
* Bounded factors. From `g = b * u`, `b = g * star u` and `b⁻¹ = u * g⁻¹`, so the
  unitary bounds apply to both. Since `‖b⁻¹ i i‖ * ‖b i i‖ = 1` and
  `‖b⁻¹ i i‖ ≤ √n * B'`, we get `(√n * B')⁻¹ ≤ ‖b i i‖`.

## Scope

The module proves only these finite-dimensional linear algebra facts. It states
nothing about adeles, number fields, compactness of the unitary group,
maximality of compact subgroups, or uniqueness of the factorization.
