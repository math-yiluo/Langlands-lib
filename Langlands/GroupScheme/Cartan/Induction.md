# Cartan containment for dimension induction

Worker 1296.

This internal, derived module supplies elementary containment steps for the
dimension induction in Milne, *Algebraic Groups* (2017), Theorem 17.91, printed
p.381/PDF p.397. Its source is registered as
`milne-2017-algebraic-groups`; the registered complete errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to 17.91.
The implemented arguments use the Library's actual closed subgroup embeddings
and all-test centralizers, rather than any rational-point density argument.

`IsGeneratedByCartanSubgroups G` abbreviates the closed-competitor generation
property for one group over one field. A competitor is only required to be
closed; it can be nonsmooth, disconnected, or nonreduced. The predicate imposes
no smoothness, affineness, connectedness, or infinitude by itself. It is the
conclusion about a fixed group in the published `CartanGenerationStatement`.

`factorsThrough_hom_iff_range_le` equates factorization of an actual group
homomorphism as a scheme morphism with inclusion of ranges on all test schemes.
The forward implication precomposes a factorization by arbitrary points; the
reverse implication evaluates range inclusion at the universal source point.
This argument does not require monicity.

`mem_torusCentralizer_comp` carries centralizing points through any group-scheme
homomorphism. It postcomposes the defining commutation equation, and retains all
refinements of the test scheme. The imported
`isClosedSubgroup_subgroupIntersectionFst` from `SubgroupIntersection` applies base-change stability of
closed immersions to the actual intersection pullback.

`IsCartanSubgroup.exists_ambient_cartan` assumes that every maximal torus of a
subgroup remains maximal after mapping into an affine ambient group. It
represents the ambient centralizer of a torus witnessing the source Cartan
predicate. The preceding commutation lemma puts the source Cartan's composite
range inside that representative. The result supplies an actual factorization
into an ambient Cartan. It does not assert that the source Cartan itself is an
ambient Cartan, or establish the maximal-torus-preservation hypothesis.

`IsGeneratedByCartanSubgroups.range_le_of_maximalTori` assumes a closed
embedding `j : M ⟶ G`, the generation property for `M`, preservation of its
maximal tori, and a closed competitor `i : H ⟶ G` containing all ambient
Cartans. Each Cartan of `M` maps into an ambient Cartan and hence into `H`.
Closed representability turns this range inclusion into a homomorphism. The
pullback universal property then factors it through the scheme-theoretic
intersection `M ×_G H`. Its projection to `M` is closed, so generation in `M`
makes that projection have full range. Every point of `M` therefore lifts to
the intersection and maps into `H`. This proves range containment on every
test scheme without a smoothness assumption on the intersection or on `H`.

Finally, `isCartanSubgroup_id_of_central_maximalTorus` uses centrality to show
that the full group represents the torus centralizer.
`isGeneratedByCartanSubgroups_of_isCartanSubgroup_id` applies the containment
premise to that identity Cartan and obtains full range.

This module does not prove the existence of a central maximal torus in a
nilpotent group, the Lie-theoretic centralizer or spanning results, the
isogeny reduction, or `CartanGenerationStatement`. Those structural inputs
remain obligations of the main proof.
