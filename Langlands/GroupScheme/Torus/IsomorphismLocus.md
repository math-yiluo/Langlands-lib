# The open isomorphism locus for two split tori

For an actual homomorphism `i : H ⟶ G` of group schemes over a scheme `S`,
`TorusIsomorphismLocus.opens i` is the union of all open subsets `U` of `S`
for which the actual base change of `i` along `U.ι` is an isomorphism.
The definition makes sense for arbitrary group schemes. The all-test equivalence
proved here assumes that both `H` and `G` are split tori over `S`.
All schemes and field-valued tests lie in an arbitrary universe `u`.

`isIso_comp_baseChange_iff` compares direct and iterated base changes by
`Descent.pullbackComparison` and its naturality. Conjugation by the two
comparison isomorphisms preserves invertibility. `underlying_isPullback`
identifies the actual square of underlying schemes with a pullback square.
`isIso_of_underlying` reflects an underlying scheme isomorphism first into
the slice category and then into actual group objects.

`isIso_of_openCover` proves locality on an open cover of the base: pull that
cover back to the target group scheme, use the preceding cartesian squares
to identify the resulting maps with underlying base changes of `i`, and apply
Mathlib's target locality of scheme isomorphisms. This is a gluing argument
for the actual morphism, with no premise supplying an inverse globally.

`exists_open_split` extends the affine neighbourhood theorem to an arbitrary
base. It chooses an affine chart through the image of the supplied field
point, applies `exists_open_affine` on that chart, and composes the resulting
open immersion with the chart. The original field-valued morphism factors
exactly through the constructed neighbourhood.

`isIso_of_range_subset_opens` proves one implication without torus hypotheses.
For a test morphism `b : T ⟶ S` whose image is in the union, the preimages of
the defining opens cover `T`. Invertibility on those opens is preserved by
base change; the open-cover lemma glues it. `isIso_opensRange` transports an
isomorphism neighbourhood from an arbitrary open immersion to its open range.

For the converse, `isIso_baseChange_iff_range_subset_opens` tests a given
base-changed isomorphism at the residue field of each point of `T`. The split
torus neighbourhood theorem produces an open neighbourhood in `S` containing
its image, over which `i` is invertible. Thus the entire image of `b` lies in
the union. Finally `isIso_baseChange_iff_factors` uses the universal property
of the open immersion `(opens i).ι` to identify this condition with actual
factorization through that immersion. It applies to every test scheme `T`,
including nonreduced and disconnected schemes.

This is an internal construction derived from the affine coefficient
certificate and standard scheme pullback and open-cover operations. It does
not claim the relative-torus descent result, smoothness, or Hom
representability; those remain separate steps toward the host task.
