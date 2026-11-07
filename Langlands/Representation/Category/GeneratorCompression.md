# Compact compression on images of generator presentations

Worker 1751. This is internal infrastructure obtained by composing the
published generator-presentation, actual coproduct-carrier, compact averaging,
and stable-endomorphism results.

`FunctorCompressionStablePower T K hK g b` means that the actual compressed
action has a stable `b`-th power on every object in the image of `T`. Stability
includes both square kernel and square range equalities. This definition
does not assert existence of such an exponent.

First, `compressedAction_stablePower_of_cofan` proves fixed-exponent stability
on any colimiting cofan from stability on every summand. The actual summation
equivalence identifies its vertex with the algebraic direct sum. Smoothness
of the latter follows from its equivariant injection into the smooth vertex.
The published fixed-vector direct-sum equivalence gives componentwise
compression powers, and the summation equivalence transfers stability.
The index and carrier universes are independent.

For an abelian source category, a generator with faithful integer-module Hom
functor supplies a right-exact presentation of every object by two coproducts
of copies of that generator. Their index types lie in the Hom universe.
An additive functor preserving finite colimits maps this presentation to a
right-exact row. Preservation of coproducts of those sizes identifies its
first two objects as coproducts of the generator image. The preceding cofan
result makes their compression powers stable with the same exponent.
Compact averaging preserves exactness on fixed vectors; the published
right-exact stable-endomorphism theorem then proves stability on the target.
This is `functorCompressionStablePower_of_generator`.

Finally, `functorCompressionStationary_of_generator` starts with one positive
stable power on the generator image. Its exponent works on every image
object, so the published stable-power criterion gives both stationary power
chains and their complementary limiting submodules from that same threshold.
The threshold is chosen before the quantified source object.

All coproduct, generator, and right-exactness conditions are explicit.
There is no admissibility, finite-dimensionality, finite-length, or finite-type
condition on the represented objects. These results do not construct a
generator, prove stability on its image, or prove the dynamic-parabolic
uniform-stabilization endpoint.
