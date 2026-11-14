# Smooth quotient kernels in ordered root coordinates

This internal support unit concerns a smooth homomorphism `q : G → Q` of
smooth affine groups over a field and a homomorphism from a split torus `S`
to `G`. No reductivity, maximality, connectedness of either ambient group,
or surjectivity on rational points is assumed.

`positiveRelativeRoots_comp_subset_of_smooth` states that the strictly positive
relative-root weights for the composite torus map into `Q` are among those for
`G`. Smoothness gives a surjective differential on each intrinsic character
space, so a vanished source weight cannot appear in the target.

`root_product_comp_eq_one_iff_of_smooth` takes an injective enumeration of all
indivisible positive roots for one cocharacter and assumes that their positive
cyclic tails are pairwise disjoint. For every test scheme, an ordered product
of points in those full positive-multiple root functors is killed by `q` if
and only if every root point is killed by `q`. This includes an empty
enumeration and retains multipliable roots through the full root functors.
`SmoothQuotientRootCoordinatesStatement` universally quantifies this assertion
at universe `u`; `smoothQuotientRootCoordinates` proves that proposition.

The proof realizes the target positive semigroup subgroup as a smooth connected
unipotent group. Its torus-action support is contained in the source positive
support by the differential argument. The published ordered semigroup-product
theorem for a larger support therefore applies to the source root-ray
partition, even when some roots disappear in the quotient. Mapping each
cyclic semigroup factor into `Q` identifies it with the corresponding full
target root functor. The resulting ordered multiplication is an isomorphism
onto the represented unipotent subgroup. Lift the images of the supplied
root points to its factors. If their product is one, monomorphy of the
subgroup inclusion and uniqueness in the ordered product force every lifted
coordinate to be one. The converse follows from preservation of multiplication.

This is derived content using the Library's smooth tangent-weight,
semigroup realization, larger-support ordered product, and cyclic root-functor
comparison theorems. It makes no new translation from original literature
and does not claim the upstairs Bruhat–Tits radical-generation theorem.
