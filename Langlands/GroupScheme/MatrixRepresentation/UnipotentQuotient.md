# Faithful representations of supplied fpqc unipotent quotients

This internal construction combines the actual exact-kernel representation
with the published fpqc homomorphism descent and local quotient-lifting
interfaces. Its conclusions follow from these existing interfaces without
another structural theorem.

For group schemes over any base scheme, `mono_of_kernel_range_le` considers a
factorization `f = q ≫ d` with `q` flat, surjective and quasi-compact. If the
full kernel range of `f` is contained in that of `q`, the underlying morphism
of schemes over the base of `d` is a monomorphism. To prove this, a test point
killed by `d` is lifted after pulling back the fpqc cover `q`. Its lift is
killed by `f`, hence by `q`, so the original point is locally the identity.
The fpqc epimorphism makes it the identity on the original test scheme.
Injectivity of the homomorphism on every test-point group then gives the
monomorphism.

Given `c : KernelCoordinates i` and a supplied fpqc quotient `q` whose full
kernel range is the range of `i`, `KernelCoordinates.descend` constructs an
actual representation of the quotient. Equality of the kernel ranges proves
that the original representation kills the full kernel of `q`, so the
published `FpqcHomDescent.hom` applies. `descend_fac` proves its pullback is
the original representation, and `descend_mono` proves its faithfulness on
every relative scheme test.

Over an arbitrary field, `exists_faithful_of_unipotent_kernel` applies this
construction to a closed unipotent normal subgroup of an affine group locally
of finite type. It returns a finite dimension and an actual faithful matrix
representation of the supplied fpqc quotient over the same field.
The quotient is supplied throughout. Its geometric affineness and the
construction of the radical quotient remain separate obligations.
