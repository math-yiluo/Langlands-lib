# Actual adjoint weights in the identity component

For a smooth affine group scheme `G` over any field and an actual
split-torus map `i : T → G`, `IdentityComponent.torusHom i hT`
is its canonical factor through the actual identity component
`identityComponent G`. Its composite with the existing inclusion
`identityComponentι G` equals the specified map `i`. A closed
immersion `i` gives a closed immersion of this factor.

`IdentityComponent.weightEquiv i hT α` identifies the existing
actual character weight space in the identity component with
the existing weight space in `G`. Its map is precisely the
differential of `identityComponentι G`; the coefficient and
torus maps are unchanged. Consequently every weight dimension,
vanishing of every weight space and the whole set `roots i`
are preserved exactly. This applies to disconnected `G`.
Neither reductivity nor algebraic closedness is assumed.

The general construction `smoothMonoWeightEquiv` works over any
commutative base ring. A smooth monomorphic map `f : H → G`
between affine group schemes has a bijective map on actual
dual-number Lie kernels: monomorphism gives injectivity and
the published smooth infinitesimal lifting theorem gives
surjectivity. The published weight-membership reflection for
a monomorphic map restricts this differential to a bijection
between each weight for `i : T → H` and the same character
weight for `i ≫ f`.

The identity-component result applies that construction to
the actual open-and-closed inclusion, which is smooth and
monomorphic. Connectedness of a split torus supplies the
canonical factor; no replacement of the original geometric
fibre or of its identity component is made.

The provenance is internal: all constructions are composed
from the existing identity component, its universal
factorization, actual Lie-kernel functoriality, smooth
infinitesimal lifting and actual adjoint weight spaces.
The file supplies the disconnected-fibre comparison needed
by the reductivity-locus proof; it does not prove relative
rank constancy or openness.
