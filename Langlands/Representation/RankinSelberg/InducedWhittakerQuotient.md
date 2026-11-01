# Actual induced quotients onto block coefficient models

This internal support module constructs the algebraic quotient comparison
needed when applying the ordinary matrix-integral route to reducible
Whittaker-type inputs. It does not establish any analytic assertion or either
rank-one-test multiplicativity proposition.

The normalized parabolic and product map surjectivity lemmas extend the
published adapters in
[InducedMapSurjectivity](../Parabolic/InducedMapSurjectivity.md) to independent
source and target carrier universes and unbundled representations. Worker 181
located those adapters and their precise universe restriction. The parabolic
proof follows the existing proof of Worker 328: the closed actual parabolic,
cofinal compact open subgroups of the actual p-adic general linear group, and
smoothness of the half-modulus twisted Levi inflations discharge the published
smooth-induction surjectivity theorem. The product proof applies the existing
external tensor-map surjectivity theorem and smoothness of a finite external
tensor product. No segment, irreducibility, admissibility, or central-character
assumption enters these map-surjectivity assertions.

`normalizedProductModelMap` is the actual normalized product intertwiner built
from the canonical quotient `Whittaker.modelMap` on every block.
`normalizedProductModelMap_surjective` applies parabolic surjectivity to the
external tensor of these canonical surjections onto the actual invariant
coefficient images.
Smoothness of these images follows from `model_isSmooth`. The block subgroups
and their characters are arbitrary supplied data, so the result also applies
to each positive-rank standard Whittaker block. Source carrier universes remain
independent of the function-space universe containing the coefficient images.
The original coefficient maps may have kernels.

`coefficientModel_functionalsComap` identifies the actual coefficient
subrepresentations for a quotient functional and its pullback along a
surjective intertwiner. Intertwining identifies the entire coefficient
functions, and surjectivity lifts their vectors. The result strengthens the
already published whole-function range equality only by packaging it as
equality of the actual invariant images.

Finally, `coefficientModel_eq_of_surjective_of_whittakerType` assumes full
Whittaker type on the source and specified nonzero source and target
functionals. Surjective pullback makes the target functional a nonzero source
functional. The published equality of source coefficient models for any two
nonzero functionals, followed by the preceding quotient equality, gives the
conclusion. It asserts equality of function subrepresentations, without
asserting that either original carrier is equivalent to its model. In its
intended induced application, full induced Whittaker type and existence of the
specified target functional must be supplied separately.

These are derived constructions from the cited Library definitions and
theorems. They introduce no new literature theorem and supply no convergence
bound, normalized generator, factor certificate, or divisibility proof.
