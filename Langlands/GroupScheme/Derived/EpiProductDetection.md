# Closed-subgroup detection by an epimorphic product

This is an internal construction and its elementary consequences for the
derived-subgroup semisimplicity proof. It uses the published all-test
represented-subgroup factorization and the actual scheme multiplication map
`subgroupProductMap`.

`subgroupProductFactor` lifts the two homomorphisms through a representative
containing their ranges, and multiplies the lifted points. Its composite with
the representative's inclusion is the original product map.

If the original product map is an epimorphism, the representative's inclusion
is also an epimorphism. For a closed immersion into an affine scheme this makes
the inclusion an isomorphism: the forgetful functor from schemes over the base
preserves epimorphisms because it has a right adjoint, epimorphisms induce
injective maps on global functions, and Mathlib's closed-immersion criterion
then applies. Consequently a closed represented subgroup containing both
factors is the whole group.

All statements concern the actual morphisms of schemes over an arbitrary base
and the subgroup functors on all test schemes. Affineness of the ambient
scheme, closed representability, and the product epimorphism are explicit
hypotheses.
