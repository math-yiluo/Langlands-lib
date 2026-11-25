# Inner-action loci from a supplied automorphism group scheme

This internal construction is the formal pullback argument for two actions
on a group scheme over an arbitrary base. It depends on the supplied
`GroupAutomorphismScheme` interface in
[`AutomorphismScheme`](AutomorphismScheme.md), which represents every
natural local automorphism on every test scheme. It asserts no existence
theorem for that representing group.

For actions `a` of `H` and `c` of `A` on `G`, `I.innerLocus a c` is the
group-scheme fibre product of their classifying homomorphisms to `I.group`.
Its two projections are `innerLocusInclusion` to `H` and
`innerLocusInnerHom` to `A`. The pullback condition and the classification
equality criterion prove that the two restricted actions agree.

The existing `subgroupIntersection_isPullback_scheme` theorem identifies
the underlying scheme square as a pullback. Stability under base change
then proves that the projection to `H` is an open immersion, respectively
a closed immersion, when the classifying homomorphism for `c` is so.
These immersion hypotheses are explicit supplied inputs.

For any group scheme `L`, compatible homomorphisms from `L` to `H` and `A`
have equal composites to `I.group`, by classification of the restricted
actions. The group-scheme pullback supplies the unique lifting
homomorphism. `exists_innerActionLocus` collects these properties.

No reductivity or centre-quotient hypothesis is used in this formal
construction. In particular, there is no smoothness, flatness, finiteness,
connectedness or affineness condition on the acting or test groups.
The construction works uniformly in the universe and for an empty or
nonreduced base. To apply it to the reductive inner-action statement one
still needs the geometric existence of a full automorphism group scheme
and the clopen-immersion property for a supplied adjoint action. This
module does not establish that geometric input.
