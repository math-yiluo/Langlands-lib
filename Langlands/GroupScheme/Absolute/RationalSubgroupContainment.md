# Closed subgroup containment detected on rational points

This is an internal, derived scheme-theoretic helper for the dynamic-centralizer
reductivity proof. It does not state a structural theorem about Borel subgroups
or unipotent radicals. Its provenance is the composition of the Mathlib
closed-point, Jacobson-space and reduced-scheme facts listed below.

Let `k` be an algebraically closed field, `i : H ⟶ G` a group-scheme
homomorphism, and `j : K ⟶ G` a closed subgroup immersion. Suppose the underlying
scheme of `H` is reduced and locally of finite type over `k`. Then containment
of the images of `H(k)` in `K(k)` implies containment of the associated range
subgroup functors on every test scheme. The converse also holds, and the
containment gives a group-scheme homomorphism `a : H ⟶ K` with `a ≫ j = i`.
There is no monicity assumption on `i`, no reducedness assumption on `K`, and
no finite-type or separatedness assumption on `G`.

The implemented proof pulls back the closed immersion `j` along `i`. Every
closed point of `H` is the image of a `k`-point by
`AlgebraicGeometry.pointOfClosedPoint`. The rational-point hypothesis places
these closed points in the image of the pullback projection. Since `H` is
Jacobson and that image is closed, the projection is surjective. A surjective
closed immersion into a reduced scheme is an isomorphism, by
`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`. Its inverse gives
a factorization of the underlying morphism of schemes over `k`, which proves
range inclusion on all test schemes. Finally, the existing
`SubgroupFunctor.IsRepresentedBy.factorHom` turns that range inclusion into a
group-scheme factorization.

The construction `factorOfAlgClosedPoints` supplies the actual homomorphism.
Its compatibility with the inclusion is `factorOfAlgClosedPoints_comp`.
The range criteria are `range_le_of_algClosed_points` and
`range_le_iff_algClosed_points`, and the existence wrapper is
`exists_factor_of_algClosed_points`. All declarations are in the namespace
`Langlands.GroupScheme.SubgroupFunctor`, at arbitrary universe `u`.
