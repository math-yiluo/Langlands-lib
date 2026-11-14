# Opposite R1 coordinates on the same root stabilizer field

This internal construction puts the published one-sign root-field coordinates
for a relative root and its negative over the same finite separable field.
It does not supply a rank-one homomorphism, an induced-torus morphism, or a
normalizer point, and does not prove algebraic or valued coordinate existence.

The fields `k` and `L` have arbitrary universe `u`. The theorem
`Langlands.GroupScheme.rootOrbitField_eq_of_neg` needs only an affine ambient
group and opposite actual roots of the base-changed torus: their stabilizer
fields are equal as intermediate fields of `L/k`. The ordinary Galois action
is additive, so fixing a character is equivalent to fixing its negative.
The proof applies `mem_rootOrbitField_iff` to this observation.

`RootFieldCoordinates.toOn` copies the coordinate equivalence, character,
restriction equation, and full-centralizer conjugation equation to the
specified-field record on the original extension.

`oppositeRootFieldCoordinatesOfTorus` assumes `L/k` finite Galois, a connected
reductive affine group `G`, a supplied maximal torus `j : T → G`, a morphism
`f : S → T` whose composite is a maximal split torus, and the equality of the
whole centralizer subgroup functor with the torus represented by `j`. It
also assumes `T` splits over `L`, an actual root datum for `j_L`, and that
both `a` and `-a` are relative roots with no higher positive multiples.
Smoothness and local finite type are present as typeclass parameters; `j`
is a closed subgroup. Supply an actual absolute root `β` restricting to `a`.

The construction uses `hP.neg_mem_roots` for the actual root `-β` and
additivity for its restriction to `-a`. The published
`rootOrbit_eq_restrictionFiber_of_torusCentralizer` identifies each sign's
restriction fiber with its Galois orbit. Apply the published
`rootFieldCoordinatesOfOrbit` separately to these two orbits. The
stabilizer-field equality then transports the negative coordinates to the
positive field without changing its character or conjugation content.
The output is a pair of `RootFieldCoordinatesOn` records over
`rootOrbitField k L j β`. This intermediate field is finite separable over
`k` since `L/k` is finite Galois.

The provenance is internal: the module combines the existing actual-root
Galois action, stabilizer fields, fiber transitivity and root-field coordinate
construction. No new literature assertion or hypothesis about quasi-split
coordinate existence is used. The two parametrizations have a common field;
compatibility with a single SL2 homomorphism remains a separate obligation.
