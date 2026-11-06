# Determinant-one diagonal action on quadratic root coordinates

This internal unit derives an explicit matrix comparison from the published SU3 coordinate embedding and intrinsic scaling maps. Its ring constructions work over an arbitrary involutive commutative ring with a scalar unit, including characteristic two and the zero ring. The valuation consequences use an arbitrary field and an explicitly supplied conjugation-invariant additive valuation to the extended real numbers. No new literature assertion is made.

`barUnit` applies the specified involution to scalar units. `diagonalRootScalar` is the unit `a = t*t/bar(t)`. The actual invertible matrix `diagonal` has entries `(t, bar(t)/t, 1/bar(t))`. The entry formulas identify its underlying matrix, and entrywise multiplication proves its identity, multiplication, homomorphism and inverse laws. Its determinant is one. Expanding the matrices also proves preservation of the already defined split Hermitian form; the cancellations use unit inverses and the involution laws. The root scalar satisfies `a*bar(a) = t*bar(t)`.

`diagonal_conjugate_embedding` expands the matrix products to prove
`D(t)*embedding(x)*D(t)⁻¹ = embedding(scale(a,x))`.
The proof cancels the right diagonal factor and checks the nine matrix entries. Since scaling by a unit is an automorphism of the actual coordinate group, this proves that `D(t)` belongs to the normalizer of the actual embedded root subgroup. More generally, `map_conj_diagonal` identifies conjugation of every embedded coordinate subgroup with its image under scaling. This follows by composing the homomorphisms and applying the same pointwise conjugation identity.

For a field with an invariant additive valuation `omega`, `diagonalRootScalar_value` proves `omega(a) = omega(t)`. The parameter is a unit, so its value is finite; multiplicativity, invariance and the inverse-value law reduce the assertion to real arithmetic. The existing scaling formulas then give a root-depth shift of `omega(t)` and a central-depth shift of `omega(t)+omega(t)`, including infinite depths.

If `omega(t)` is the finite real value `s`, conjugation sends the embedded root filtration at level `r` exactly onto the embedded root filtration at `r+s`. It sends the embedded ambient central filtration at level `r` exactly onto the one at `r+2*s`. These are equalities of subgroup images, rather than just inclusions. The proofs combine `map_conj_diagonal`, the existing shifted filtration preimage laws, and surjectivity of the scaling automorphism. The central filtration here is the subgroup of the full coordinate group with first coordinate zero.

These results concern the explicit matrices and coordinate group. Representability, identification with a centralizer or relative root subgroup of an arbitrary reductive group, primitive reflection translations, and the exact facet-fixing theorem remain separate obligations.
