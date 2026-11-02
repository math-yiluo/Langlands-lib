# Smooth full endpoint-kernel projections for actual Picard arrows

This internal construction supplies smoothness and scheme representability
of every full base change of an endpoint-kernel projection. It uses the
actual smooth relative automorphism hypothesis, rather than an assumed
quotient or a geometric-point criterion.

`totalParallelIsomorphismRepresentation` totalizes the smooth slice
representatives of parallel actual arrows. The corresponding natural
isomorphism preserves the common base projection exactly.
`exists_smoothEndpointPullback` transports the complete presheaf pullback
of parallel arrows through that representation. Thus for fixed endpoints
with a given actual arrow, their full endpoint base change is represented
by an actual scheme smooth over the common base.

`smooth_endpointKernel_projection` applies this construction to every
scheme test of any presheaf endpoint kernel. A map from a scheme into
the actual arrow presheaf supplies, by Yoneda, both endpoint maps and
an actual bundle isomorphism. The previous construction then gives a
smooth scheme representing the outer endpoint pullback. Cancelling the
right kernel pullback square gives the full base change of the kernel
projection. The relative morphism-property constructor verifies both
representability and smoothness on all such base changes, not just the
chosen presentation. Applying the same lemma to the flipped kernel
square also handles its other projection. No sheaf section is assumed
to have a global bundle representative and no quotient is constructed
by this lemma.
