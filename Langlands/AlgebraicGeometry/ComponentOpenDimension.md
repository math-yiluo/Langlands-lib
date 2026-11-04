# Dimension of open intersections with components

This derived topological prerequisite supports the chart comparisons for
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp. 5–6, Theorem 3.4(2). The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It is an internal prerequisite rather than a numbered source assertion.

`subtypePreimageCommHomeomorph S T` constructs the actual homeomorphism
between the two iterated subspaces representing the intersection of S
and T. It preserves the underlying point. `openInSubspace S U` is the
actual inverse image of an ambient open U in the subspace S.

`topologicalKrullDim_open_eq_of_openCover` proves that constancy of
dimension on nonempty opens can be checked on an arbitrary open cover
of a preirreducible space. The cover and space have independent
universes. Empty cover members are allowed. Given a nonempty open V,
every nonempty cover member meets V by preirreducibility. Constancy on
that member identifies its dimension with that of the intersection,
which is at most the dimension of V. Empty members are subspaces of V.
The open-cover dimension formula gives the upper bound for the whole
space; subspace monotonicity gives the reverse bound.

`closure_image_mem_irreducibleComponents_open` proves that the closure
in the ambient space of a component of an open subspace is an ambient
irreducible component. Extend its actual image to a maximal irreducible
set. The preimage of that ambient component is a component of the open,
and maximality of the original component forces equality. The image is
dense in the ambient component, so its closure is exactly that component.
`preimage_closure_image_irreducibleComponent_open` proves that restricting
this closure to the original open recovers the original component exactly.
These component statements require no Noetherian or separation hypotheses.
