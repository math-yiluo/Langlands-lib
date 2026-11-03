# Closed-representability reductions for character-kernel centralizers

This derived unit uses the existing scheme-theoretic kernel, its commutative
group law, and the actual all-test centralizer. `characterKernelComm` retains
the inherited commutative structure on exactly the existing character kernel;
it introduces no different subgroup.

`characterKernel_isAffineHom` proves that a character kernel is affine when
the source commutative group scheme is affine, over an arbitrary scheme base.
The target multiplicative group is affine and hence separated. The existing
kernel inclusion is therefore a closed immersion. Composing this affine
inclusion with the affine structure morphism of the source proves affineness
of the kernel. No smoothness, reducedness or primitivity is used.

`kernelCentralizer_eq_torusCentralizer` identifies the existing kernel
centralizer with the all-test centralizer of the composite of the actual
kernel inclusion and the chosen map to the ambient group. The proof restricts
conjugation along the inclusion and uses the existing conjugation-centralizer
identity for commutative acting groups.

The two `kernelCentralizer_isClosedRepresentable_of_...` theorems are conditional
reductions over any field and retain the explicit general field fixed-subgroup
or centralizer representability statement as a premise. Affineness of the
source gives affineness of its kernel, so those statements apply directly.
The ambient group need not be affine or smooth for these reductions.
The character need not be nonzero, and the source need not be a split torus.

These are internal consequences of the published constructions and restriction
identities. They supply neither a proof of the general representability
premises nor smoothness of the representative.
