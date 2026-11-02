# Finite intersections of affine open subfunctors

This internal development supports the construction of an invariant affine open
in the scheme-representability argument for separated commutative group algebraic
spaces. Its definitions refer to presheaves on all schemes over a base, without
requiring a sheaf or group structure.

`IsAffineOpen A` means that the actual inclusion of the subfunctor A is a
representable open immersion and that A is naturally isomorphic to the scheme
Yoneda presheaf of an actual affine scheme over the base.

`range_intersection` identifies the range of a represented fibre product with
the intersection of the two chart ranges. It uses the pullback range formula
from OpenSubfunctorLifting and the elementary image-of-inverse-image identity
for sets.

When the base is affine and the ambient presheaf has representable closed
diagonal, `IsAffineOpen.inf` proves that the intersection of two affine open
subfunctors is affine open. The proof chooses their representing schemes, takes
the represented intersection from AffineIntersections, and uses its affineness
and open projection. The range identity identifies that chart with the
intersection subfunctor on every test scheme. Its factorization through the
subfunctor is an isomorphism because its components are bijective. Openness of
the inclusion then follows by cancellation of that isomorphism.

`isAffineOpen_biInf_finset` applies this binary result by induction to any
nonempty finite set of indices. The singleton case uses its given affine
representation. `isAffineOpen_iInf` specializes this to a nonempty finite
index type, of arbitrary universe, by using its finite set of all indices.
The nonempty hypothesis is essential here: the empty intersection would be
the entire ambient presheaf, which has not been assumed affine or representable.

`isIso_fromPreimage` proves that inverse image along an isomorphism of ambient
presheaves is naturally isomorphic to the original subfunctor: the restricted
map has an inverse given by the inverse ambient isomorphism. Consequently,
`IsAffineOpen.preimage_iso` transports an affine open representation along an
arbitrary ambient isomorphism, over any base.
`IsAffineOpen.iInf_preimage_iso` combines this with the finite-intersection
theorem. It applies to any nonempty finite family of automorphisms; no action
or stability assertion is assumed or proved in this module.

The helper `isOpenImmersion_schemeYoneda_map` supplies the open-immersion
property of scheme Yoneda applied to a scheme open immersion. It constructs a
represented pullback on each scheme test and applies stability under base
change to the underlying scheme square.

All assertions are derived from the imported Library constructions and
Mathlib's relative morphism-property and subfunctor APIs. No independent
literature assertion is introduced.
