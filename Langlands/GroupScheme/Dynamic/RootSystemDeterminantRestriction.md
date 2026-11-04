# Opposite weight spaces from the supplied actual root system

This internal construction supplies
`HasRelativeRootSystem.negWeightSpaceEquiv`, a linear equivalence between the
actual character weight spaces for `α` and `-α`. The field has arbitrary
characteristic and universe `u`. The torus is split, its map into the affine
group scheme is a monomorphism, and the actual relative-root-system predicate
is a hypothesis. Connected reductivity, an integral coroot system and
finite dimensionality are not extra hypotheses of this construction.

For an actual relative root, the published
`HasRelativeRootSystem.exists_isRelativeReflection` produces a reflection in
the actual relative Weyl quotient. A rational normalizer representative exists
by quotient surjectivity. Its action sends `α` to `-α`: the reflection formula
first gives this equality after rationalization, and splitness makes
rationalization of the character lattice injective. The existing
`map_weightSpace_weylAction` identifies the image of the weight space under
the adjoint map with the opposite weight space. The inverse adjoint map makes
this map injective, so `Submodule.equivMapOfInjective` gives the desired
equivalence. At zero, the two weight submodules are equal. At a nonzero
nonroot, both submodules are zero, using the published stability of relative
roots under negation.

The implemented consequences are equality of opposite weight multiplicities
and
`positiveWeightCharacter i (-ζ) = -positiveWeightCharacter i ζ`.
The latter reindexes the character sum by negation and uses the multiplicity
equality. These results use the already supplied `HasRelativeRootSystem i`,
without assuming `RelativeRootReflectionExistenceStatement`.

For arbitrary represented models of the centralizer of `ζ` and `-ζ`, the two
unipotent groups, a factorization `j : T → Z` of the actual torus map, and finite
Lie coordinates, the final two theorems prove that the sum of the opposite
determinant characters restricts to zero on `T`, and that their values multiply
to one at every point in the image of `T(k)`. They retain the affine and
finite-type hypotheses used by
`characterRestrict_centralizerAdjointDeterminant`. Restriction and evaluation
refer to these same characters and maps.

The provenance is a deduction from the named Library declarations.
The proof body uses relative Weyl reflections, adjoint weight transport,
linear equivalences, character restriction, character sums and evaluation.
The reciprocity reduction module is imported for its existing positive-weight
character and torus-restriction formula. Its stronger theorem requiring
central split character detection and reductivity of dynamic centralizers is
not applied. Representation modules occur in the import closure; no geometric
lemma, adjointness, cuspidal-support, character-independence or Langlands
classification theorem is used in these proof bodies.

The construction does not extend the character identity from `T` to all of
`Z`, prove opposite Haar reciprocity on all centralizer points, or establish
the common-Levi squared-modulus identity or rational exact-K0 expansion.
Those remain separate obligations of the host task.
