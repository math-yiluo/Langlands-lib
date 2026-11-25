# Monomorphisms from reductive groups to smooth affine groups

For any scheme `S : Scheme.{u}`, reductive group scheme `H` over `S`, smooth
affine group scheme `G` over `S`, and homomorphism `f : H ⟶ G` monomorphic
on underlying schemes, `ReductiveImmersion.isImmersion_of_mono` proves that
that underlying morphism is an immersion. There is no Noetherian, global
splitting or global affine base assumption.

`closedSplitTorusImages_of_mono` first discharges the explicit torus-image
premise of the etale local reductive immersion criterion. It needs only an
affine target locally of finite type. After each affine etale base change,
the target retains those properties and the base-changed map is monic.
A closed coordinate split torus inclusion is also monic, so their composite
is monic. `IsSplitTorus.isClosedSubgroup_of_mono` proves it is closed.
Smoothness supplies local finite type in the final immersion theorem, and
`isImmersion_of_closedSplitTorusImages` applies with no remaining torus
image premise.

The module constructs `immersionOpen`, the actual largest open subset of
the target in which the image is closed, and `closedFactor`, the actual
closed immersion of the source into that open. `closedFactor_ι` identifies
their composite with the original underlying scheme morphism. These are
the Mathlib coborder and lift constructions applied to the proved
immersion.

This is an internal composition of the etale local reductive immersion
criterion and arbitrary-base split torus monomorphism closedness, followed
by the standard coborder factorization. It asserts no separate translation
of external literature. The conclusion remains immersion into a smooth
affine target; it does not assert global closedness or treat the arbitrary
separated finitely presented targets of `ReductiveMonomorphismClosedImmersionStatement`.
