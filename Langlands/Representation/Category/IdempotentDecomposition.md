# Natural idempotents and constituent categories

This internal construction uses the existing category of smooth complex
representations of an arbitrary topological group. The group and carrier
universes remain independent. The construction needs no finite length,
admissibility, or finite dimension.

`idempotentComponents A p` is the actual kernel at `false` and actual range at
`true`. `idempotentCofan A p` has their literal inclusions into `A`. When `p` is
idempotent, `idempotentCofanIsColimit` supplies its coproduct universal property:
a pair of maps extends by applying the range map to `p v` and the kernel map to
`v - p v`. The two summands add to `v`, which also proves uniqueness.

`irreducibleSubquotientProperties P` has the all-`P` factor at `true` and the
no-`P` factor at `false`, testing every actual irreducible subquotient.
`irreducibleSubquotientProperties_offDiagonalHomsZero` proves orthogonality for
these two factors without assuming any decomposition. A nonzero morphism has a
nonzero actual image and thus an irreducible actual subquotient. That object
occurs in both its source and target, contradicting their two constituent
conditions.

`categoryDecomposition_of_natural_idempotent` assumes a natural family of
idempotent intertwiners and the criterion that, for every irreducible object
`D`, the projector fixes every vector exactly when `P D`. Naturality makes the
projector identity on its range and zero on its kernel; each of these scalar
actions passes to actual subquotients by injectivity of the occurrence map and
surjectivity of the quotient map. The criterion gives the all-`P` property on
the range. A `P` irreducible subquotient of the kernel would have both identity
and zero action and hence would be zero, contradicting irreducibility. The
actual coproduct and the orthogonality theorem give the existing
`Renard.IsCategoryDecomposition` predicate.

The provenance is internal algebraic assembly of the published smooth
subrepresentation and subquotient constructions, subquotient transitivity,
irreducible-subquotient existence, and the existing Appendix A.IX definition.
The result does not construct a projector or prove its irreducible test in a
particular application. Those remain explicit inputs.
