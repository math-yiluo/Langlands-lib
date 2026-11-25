# Proof of bounded normalized inverse-pair finiteness

`Langlands.Algebra.Rosenlicht.boundedInversePairs` proves the published
Library statement `Langlands.Algebra.RosenlichtBoundedInversePairsStatement.{u,v}`,
with independent universes for the field and the domain.
It asserts finiteness of normalized inverse pairs in two finite-dimensional
subspaces of a commutative domain over an algebraically closed field.
No finite-type hypothesis on the domain is used.

This is an internal algebraic proof for the Rosenlicht tensor-unit
development, rather than a claimed transcription of the compactification
and divisor argument in Milne. The direct imports are
`Langlands.Algebra.RosenlichtBoundedInversePairsStatement` (the unchanged
published statement), `Langlands.Algebra.RosenlichtPolynomialFiniteness` and
`Mathlib.LinearAlgebra.Dual.Lemmas`.

The linear-form helpers construct homogeneous linear polynomials with
prescribed coefficients and compute their evaluations.
`matrix_zero_of_minors` assumes two finite linearly independent families
`v i` and `w j` in the domain. If the two-by-two minors of a matrix `x`
vanish and the sum of `x (i,j) • (v i * w j)` is zero, the matrix is zero.
To prove this, suppose a pivot entry is nonzero. Expand the product of
its column combination of the `v i` and its row combination of the `w j`.
The minor relations identify this product with the pivot entry times the
full product combination, hence with zero. The domain hypothesis makes
one combination zero. Linear independence forces all coefficients of that
combination to vanish, contradicting the nonzero pivot.

`finite_normalized_rankOne` applies the homogeneous-chart lemma to matrix
coordinates. Choose any scalar coefficients `c (i,j)` and let `L` be their
linear form. Generate a homogeneous ideal by the two-by-two minors and
the linear forms whose coefficients are
`φ (v i * w j) - c (i,j) * φ 1`, for all `k`-linear maps `φ : B →ₗ[k] k`.
The latter equations say that the product combination equals `L(x) • 1`.
Linear functionals separate points of the vector space `B`, including when
it is infinite-dimensional. Consequently a common zero with `L(x) = 0`
has zero product combination; the preceding matrix lemma makes it zero.
Homogeneous-chart finiteness now shows that the rank-one matrices with
product combination one and `L(x) = 1` form a finite set.

Finally choose finite bases of the two subspaces. Send a normalized inverse
pair to the outer product of its two coordinate vectors. Set
`c (i,j) = epsilon (v i) * epsilon (w j)`. The outer product has vanishing
minors, its product combination is one, and applying `epsilon` shows its
`L`-value is one. This maps pairs into the finite set just constructed.
The map is injective: summing each row against `epsilon (w j)` recovers
the first coordinate vector because the second factor is normalized.
The first element of the pair is thus recovered. Its nonzero product
with the second element is one, so cancellation recovers the second
element. Finiteness follows by this injection.
