# Conjugacy of systems of matrix units

Author: Worker 5397.

This is an internal linear-algebra unit in the namespace
`Langlands.LinearAlgebra.MatrixUnitConjugation`. It works over an arbitrary
field `F` and a finite index type `m` with decidable equality.

`unitColumnMatrix E p v` is the square matrix whose `j`-th column is the
vector `E j p *ᵥ v`, that is, `Matrix.of fun r j => (E j p *ᵥ v) r`. It is the
matrix `P` used below.

`exists_mul_single_eq` takes a family of square matrices `E i j`, indexed by
`i j : m`, that satisfies the matrix-unit relations
`E i j * E k l = (if j = k then E i l else 0)`. It also takes one index `p`
with `E p p ≠ 0`. The conclusion is an invertible matrix `P : GL m F` such
that `P * single i j 1 = E i j * P` for all `i j`. Here `single i j 1` is the
standard matrix unit. So `P⁻¹ * E i j * P` is the standard matrix unit for all
`i j`.

## Proof

Because `E p p` is nonzero, some vector `w` has `E p p *ᵥ w ≠ 0`; otherwise
the columns of `E p p`, obtained from the standard basis vectors, would all
vanish. Put `v = E p p *ᵥ w`. The relation `E p p * E p p = E p p` gives
`E p p *ᵥ v = v`. The relations also give
`E i j *ᵥ (E k p *ᵥ v) = (if j = k then E i p *ᵥ v else 0)`.

The matrix `P` is `unitColumnMatrix E p v`, so column `j` of `P` is
`E j p *ᵥ v`. Column `k` of
`E i j * P` is `E i j *ᵥ (E k p *ᵥ v)`. Column `k` of `P * single i j 1` is
column `i` of `P` when `k = j` and zero otherwise. The previous identity shows
that these agree.

For injectivity, suppose `P *ᵥ c = 0`. Then `P *ᵥ c = ∑ j, c j • (E j p *ᵥ v)`.
Applying `E p k` and the relations leaves `c k • v`, so `c k • v = 0`. Since
`v ≠ 0`, every `c k` is zero. So `P` has trivial kernel, and Mathlib's
criterion `Matrix.exists_mulVec_eq_zero_iff` shows that its determinant is
nonzero. Hence `P` is a unit and defines the required element of `GL m F`.

The unit is used to replace a split central simple algebra's chosen matrix
units by the standard ones. The lemma asserts only the matrix statement above.
