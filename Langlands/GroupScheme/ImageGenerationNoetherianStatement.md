# Noetherian finiteness inputs for image generation

This is an internal prerequisite interface for the pointed-image generation
proof. Its two assertions are isolated from the geometric construction so that
their proofs can be checked and published separately. The interface follows
Worker 1378's `ImageGenerationNoetherian` proof design and the corresponding
Mathlib notions; it is not a transcription of a numbered literature assertion.

`NoetherianPrimeChainStabilizationStatement` says that an antitone sequence of
prime ideals of any Noetherian commutative ring in universe `u` is eventually
constant. Primality of every term is part of the hypothesis. The statement does
not assert stabilization for arbitrary decreasing sequences of ideals.
This is the ring-theoretic input for increasing sequences of integral schematic
images in a fixed Noetherian affine scheme.

`NoetherianAffineClosedEndomorphismStatement` says that every actual closed
immersion from a Noetherian affine scheme to itself is an isomorphism. The
scheme need not be reduced or irreducible, and no field or characteristic is
specified. This is the input for inverting a shear endomorphism of the square
of a closed submonoid.

`NoetherianImageGenerationFinitenessStatement` is exactly the conjunction of
these two propositions. This file defines proof targets only. Product-image
stabilization, subgroup construction, and the pointed-image generation theorem
remain separate obligations.
