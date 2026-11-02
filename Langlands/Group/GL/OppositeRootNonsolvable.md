# Opposite root groups force nonsolvability

This internal helper proves an abstract-group obstruction used in the general
linear Borel proof. Its source motivation is Milne, *Algebraic Groups* (2017),
Definition 17.6 and Example 17.7, printed pp.353–354 (one-based PDF pp.369–370),
source ID `milne-2017-algebraic-groups`. The elementary root-group argument is
a derived internal proof route, rather than the Lie–Kolchin argument in that
example.

Let `K` be an infinite field, let `i ≠ j` be two indices, and let `H` be any
abstract subgroup of `GL_n(K)` containing every transvection in positions
`(i,j)` and `(j,i)`. The theorem `not_isSolvable` proves that `H` is not solvable.
There is no restriction on the characteristic. All matrices are the published
`Langlands.GeneralLinear` and `transvectionUnit` constructions.

The implementation first multiplies three root elements to form a Weyl element,
and then multiplies two Weyl elements to form a diagonal matrix `D(s)` whose
entries in positions `i` and `j` are `s` and `s⁻¹`. The matrix identities are
proved for nonzero `s` by expanding products of single-entry matrices and by
checking entries. The conjugation relation gives
`[D(s), U(c)] = U((s*s - 1)*c)`.

An infinite field contains an `s` outside `{0,1,-1}`. Thus `s*s - 1` is nonzero,
and division expresses every root element as a commutator of elements of `H`.
The same argument with the two indices swapped applies to the opposite root.
Induction shows that both root groups lie in the image in `GL_n(K)` of every
derived subgroup of `H`. The nonidentity element `U(1)` therefore belongs to
every derived subgroup of `H`. Mathlib's
`not_isSolvable_of_mem_derivedSeries` concludes the proof.
