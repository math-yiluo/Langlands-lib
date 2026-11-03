# Normality and leastness of represented fppf subgroup products

These derived laws concern the existing `SubgroupFunctor.IsFppfProduct`
predicate over any base scheme `S : Scheme.{u}`. They work on every relative
scheme test, including nonaffine and nonreduced tests, and require no
smoothness, finite type, connectedness, field, or unipotence hypothesis.
They neither construct a product representative nor prove geometric properties
of one.

The provenance is internal: the laws follow from the published subgroup
functor and fppf-local product definitions, group identities, and descent for
represented monic subgroups. No external structural theorem about algebraic
groups is assumed.

`SubgroupFunctor.IsFppfLocal A` means that membership in `A` descends along
every flat, surjective, locally finitely presented map of relative test
schemes. This internal predicate records the membership reflection needed
for leastness. `isFppfLocal_range` proves it for the image of any group-scheme
homomorphism that is a monomorphism on underlying relative schemes.
`IsFppfProduct.isFppfLocal` specializes it to a supplied product
representative, using the closed-immersion field.

`FppfLocallyInProduct.conj` proves that conjugation preserves local product
membership when both factors are normal on all tests. Pull the conjugating
point back to the cover in a supplied factorization, conjugate the two
factors there, and use the group identity that conjugation preserves
multiplication. `IsFppfProduct.isNormal` applies this construction to the
membership equivalence of a supplied representative.

`FppfLocallyInProduct.mem_of_le` proves that a locally factored point
belongs to any fppf-local subgroup functor containing both factors. On the
supplied cover the two factors belong to that subgroup, so their product
does; fppf-locality reflects membership to the original test.
`mem_range_of_le` specializes this result to represented monic subgroups.
Mathlib's fppf effective-epimorphism instance in
`AlgebraicGeometry.Sites.Fpqc` and the published
`mem_range_of_comp_mem_range` descend the factorization through the
monomorphism to the original test. The cover need not be quasi-compact.

`IsFppfProduct.le_of_isFppfLocal` expresses leastness among fppf-local
subgroup functors, and `le_range` specializes it to represented monic
subgroups. `IsFppfProduct.le_range_iff` combines it with the published
two factor inclusions: containment of the local product is equivalent to
containment of each factor. The target functor must satisfy membership
descent, either explicitly or by a monic representative.

For ground-field radical existence these laws supply all-test normality
and containment once a product representative is available. Existence of a
represented smooth connected unipotent product and existence of a maximal
candidate remain separate obligations.
