# Torus containment in represented dynamic parabolics

This is an internal deduction from the published all-test subgroup functors,
their factorization construction in `Rational.LeviFactorization`, and the
explicit proposition `GenericMinimalParabolicStatement`. It introduces no
structural group theorem.

For any commutative group scheme `T` over any base scheme, every point in
the range of `i : T.toGrp ⟶ G` centralizes `T` on every test scheme.
Consequently it lies in the dynamic centralizer and then the dynamic
parabolic of each cocharacter through `T`. This proves
`range_le_dynamicParabolic` without splitness or reductivity.

`Dynamic.parabolicTorusFactor` applies the existing represented-subgroup
factorization to this inclusion. Its composite with the representing
embedding is exactly `i` as a group-scheme homomorphism.

`exists_minimalParabolic_containing_of_genericMinimal` takes the unproved
structural proposition `GenericMinimalParabolicStatement` as an explicit
premise, together with a maximal split torus and a supplied generic
cocharacter. It extracts an actual minimal parabolic representative from
that premise. Its embedding is a closed immersion, hence monic, and the
factorization just constructed puts the original torus in this actual
minimal parabolic. The result is an equation of homomorphisms over the
ground field, rather than an inclusion tested only on rational points.

The deduction works at arbitrary universe `u`, including finite fields and
empty relative root sets. It does not prove generic-cocharacter existence,
the generic minimality premise, conjugacy, or rational Bruhat decomposition.
