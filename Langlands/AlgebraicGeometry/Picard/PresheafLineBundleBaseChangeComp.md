# Universal bundles under composite restriction of the base

This internal construction compares restriction of a presheaf and its coherent
line bundle along `p : U ⟶ S` and then `q : V ⟶ U` with restriction along
`r : V ⟶ S`, given `q ≫ p = r`. It allows independent scheme and presheaf-value
universes.

The presheaf comparison uses the standard associator and the slice-category
composition and congruence isomorphisms. Transporting a supplied direct
representation along the inverse comparison gives a representation of the
successive restriction on exactly the same parameter scheme.

For any coherent presheaf line bundle, the corresponding universal bundles are
isomorphic on that same scheme. The proof applies its cartesian comparison to
the standard slice morphism from the iterated object to the direct object.
That morphism has underlying scheme map the identity. The identity-pullback
comparison therefore removes the pullback and gives the stated isomorphism.
This derives the result from the existing coherent-bundle data and standard
slice comparisons; it supplies no representability or ampleness existence
theorem.
