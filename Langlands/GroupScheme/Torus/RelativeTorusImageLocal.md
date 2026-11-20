# Étale-local closed factorizations of relative torus maps

Let a relative torus map to an affine group scheme locally of finite type over
the same base. Refine a splitting cover of the torus by affine open covers.
Over each affine piece, the split-torus factorization gives a basic open around
each prime and a closed split-torus factorization of the map over that open.
These basic opens cover the affine piece, so the composite cover is étale and
jointly surjective over the original base.

`Factorization.ofComp` transports a closed factorization from an iterated
base change to base change along the composite using the natural pullback
comparison isomorphisms. The split torus in the factorization stays fixed.
Composing with the isomorphisms preserves closedness, flatness and
surjectivity. Naturality identifies the composite homomorphism with the
base change of the original map.

This internal construction assembles the local split-torus coordinate
factorizations into the cover used for descent of the schematic image.
