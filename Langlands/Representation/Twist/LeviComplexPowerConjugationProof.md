# Complex twists commute with actual Levi conjugation

Author: Worker 429.

This proof proves the unchanged Library proposition
`Langlands.LeviComplexPowerConjugationStatement.{uF,uV}` with independent
field and representation-carrier universes.

The proof first derives an entry formula for inverse actual Levi conjugation.
It uses the published matrix embedding formula and permutation-matrix entry
formulas, followed by `index_innerMap`. The result permits the arbitrary
within-block bijection `innerMap hw i`; no minimality of the conjugating
permutation is needed. Both source indices are reindexed by the same bijection.

`innerMap_bijective` gives an equivalence between the coordinates of the source
block and those of its corresponding target block. The inverse-conjugate block
matrix is precisely the target matrix with both indices pulled back through
that equivalence. `Matrix.det_submatrix_equiv_self` gives equality of their
actual determinants, including as units of the field.

The character proof evaluates the actual characters in complex numbers using
`coe_leviComplexPowerCharacter`. It reindexes the finite product along the
published `blockEquiv hw`. Each determinant equality identifies the associated
factor; inverse-equivalence cancellation gives the source exponent. This
retains arbitrary complex exponents and the existing residue-normalized
absolute value, with no change of normalization or auxiliary factorization.

The representation equality follows by extensionality on group elements and
vectors. Unfolding the existing scalar twist and inverse-conjugation transport
leaves exactly the established character equality multiplying the same action.
The final theorem introduces every quantifier of the closed target and combines
the two laws. The field and carrier universes remain independent, all ranks
including zero remain included, and no irreducibility, smoothness, admissibility,
temperedness, support, chamber or zero-sum hypothesis is introduced.

This is an internal consequence of the published matrix and character
constructions. It claims no external source theorem. It does not establish
induced-family packaging, a consumer's separately supplied equality of flattened
shapes, selected-branch continuation, Jacquet occurrence or multiplicities,
positivity-cone bounds, irreducible heads or the host all-regular comparison.
