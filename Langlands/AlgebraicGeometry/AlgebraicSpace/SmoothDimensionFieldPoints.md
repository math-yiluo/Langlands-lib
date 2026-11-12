# Actual field points in the finite dimension decomposition

This internal supporting unit uses the actual point-selected open subspaces in
`SmoothDimensionRestrictions`. It assumes a `SmoothTargetPointDimensions f`
and works over any coefficient ring and any field with that coefficient action;
the field need not be finite.

`fieldPointIndex` evaluates the supplied target dimension at the ordinary point
of an actual field-valued section. The spectrum of a field is a singleton, so
the entire section satisfies the defining condition of that dimension
subfunctor. `fieldPointFactor` is therefore the same section, with the proof of
membership in the actual target open subspace. Its composite with the inclusion
is the original section.

Any other factorization through an occurring dimension stratum satisfies that
stratum's defining dimension equality at the field's unique point. This proves
uniqueness of the index and `existsUnique_fieldPointFactor`. Finally,
`surjective_fieldPoints_of_restrictions` lifts the factored target section in its
selected stratum and includes the resulting source section in the original
source. The preimage-subfunctor definition makes the required equality the
underlying equality of sections.

The provenance is the actual source and target subfunctor construction, the
finite index from `SmoothDimensionOpenSubspaces`, and the singleton spectrum of
a field. No estimate, Henselian lifting assertion, or adelic openness result is
assumed or proved in this unit.
