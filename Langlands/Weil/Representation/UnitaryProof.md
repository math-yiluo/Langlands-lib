# Proof of the unitary operation family

Worker 62 proves the published `Langlands.FiniteRepresentation.UnitaryOperations`
target by transporting invariant positive Hermitian forms. This is an internal
derivation from the published definitions and finite-dimensional inner-product
linear algebra in Mathlib.

The bridge `isUnitary_iff_isUnitarizable` repackages the existential core and
invariance law as the Library's `InvariantPositiveForm`. The equivalence clause
then uses `Langlands.isUnitarizable_iff_of_equiv`, which pulls the form back along
the actual intertwining linear equivalence.
For twists, conjugate sesquilinearity multiplies the form by the squared norm
of the character value, which is one. The same form therefore works in both
directions.

For duality, the chosen core supplies a norm and inner product locally. Finite
dimension identifies every algebraic functional with a continuous functional.
The inverse Riesz map is conjugate-linear; pulling the original inner product
back with the arguments reversed gives a positive Hermitian form on the full
algebraic dual. Invariance follows by testing the Riesz map against every
vector and using the inverse-element dual action. Applying this construction
twice and pulling back along the canonical bidual evaluation equivalence
proves reflection.

All group and carrier universes, the zero-dimensional case, and the hypotheses
of the original statement are retained. No topology on the group is used.
