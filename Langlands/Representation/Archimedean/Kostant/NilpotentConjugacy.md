# Conjugacy of nilpotent matrices

This module proves two standard linear-algebra facts used in the orbit part of Kostant's
theorem. It imports only Mathlib. Index sets are `Fin m`, ordered as usual. A matrix `U` is
*strictly upper triangular* if `U p q = 0` whenever `q ≤ p`. Its *superdiagonal* entries are the
`U p q` with `q = p + 1`.

* `exists_conj_strictUpper`: every nilpotent complex `m × m` matrix `M` has an invertible `g`
  such that `g M g⁻¹` is strictly upper triangular. `exists_conj_strictUpper_field` is the same
  result over any field.
* `exists_conj_of_regular`: two complex strictly upper triangular `m × m` matrices `U` and `V`
  whose superdiagonal entries are all nonzero are conjugate: `g U g⁻¹ = V` for some invertible
  `g`. `exists_conj_of_regular_field` is the same result over any field.

Neither statement is in Mathlib in this form. Both are textbook results: the first is the
nilpotent case of triangularization, and the second says that such a matrix is regular
nilpotent, that is, conjugate to the single Jordan block.

## Proofs

**Triangularization.** `exists_basis_strictUpper` works by induction on `d = finrank V`. It
shows that a nilpotent endomorphism `f` has a basis `b` indexed by `Fin d` with
`f (b q) ∈ span {b p | p < q}`. A nilpotent map is not injective, so we can pick `y ≠ 0` with
`f y = 0`. Choose a complement `W` of `K ∙ y`, and let `P : V → W` be the projection along
`K ∙ y`. Since `f` kills `K ∙ y`, we have `f x = f (P x)`. So `(P ∘ f|_W)^j = P ∘ f^j` on `W`,
and the compressed map `g = P ∘ f|_W` is nilpotent. Induction gives a basis `b'` of `W` for `g`.
The basis `Basis.mkFinCons y b'` of `V` (that is, `y` followed by `b'`) has the required
property, because `f (b' q) - g (b' q)` lies in `K ∙ y`.

For the matrix statement, apply this to `Matrix.toLin' M`. Take `g` to be the change-of-basis
matrix from the standard basis to `b`, with inverse the change of basis in the other direction.
Then `g M g⁻¹` is the matrix of `f` in the basis `b`
(`basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`). Its entry `(p, q)` is the
`p`-coordinate of `f (b q)`, which vanishes unless `p < q`.

**Regular nilpotent matrices.** Let `U` be strictly upper triangular with nonzero superdiagonal.

* `strictUpper_pow_apply_eq_zero`: `(U^k) p q = 0` whenever `q < p + k`.
* `regular_pow_apply_ne_zero`: `(U^k) p q ≠ 0` whenever `q = p + k`. In the product formula for
  `(U^{k+1}) p q`, the only possibly nonzero term is `r = p + k`, and it equals a product of two
  nonzero entries.

For `m = n + 1`, `cyclicMatrix U` is the matrix `C` whose column `q` is `U^{n-q} e_last`. Then
`U C = C J` (`cyclicMatrix_mul`), where `J = superdiagOne (n + 1)` has ones on the superdiagonal
and zeros elsewhere. Column `q` of `U C` is `U^{n-q+1} e_last`. For `q > 0` this is column
`q - 1` of `C`, which is column `q` of `C J`. For `q = 0` it is `U^{n+1} e_last = 0`, by the
vanishing lemma. `C` is upper triangular with nonzero diagonal entries `(U^{n-q}) q last`, so it
is invertible (`isUnit_cyclicMatrix`, via `Matrix.det_of_isUpperTriangular`). Hence
`C⁻¹ U C = J` (`exists_conj_superdiagOne`; the case `m = 0` is trivial). Conjugating `U` and
`V` to `J` and composing gives `exists_conj_of_regular_field`.
