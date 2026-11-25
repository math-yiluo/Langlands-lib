# Actual torus descent for a supplied pinned Galois action

This internal construction supplements `PinnedGaloisDatum` and
`PinnedGaloisBorel`. For fields `k` and `K` in universe `u`, an affine group
scheme `G` over `Spec K`, a split pinning `p`, and a supplied based action
`ρ : Gal(K/k) →* p.basedRootDatumAut`, it retains the actual torus maps
of the semilinear pinned isomorphisms.

`galoisSemilinearTorusIso` is the underlying group-scheme isomorphism of
the torus part of `p.semilinearPinnedIso`. Its inclusion square follows
from the pinned isomorphism's square. These definitions require no
finite-degree hypothesis.

For finite Galois `K/k`, `galoisTorusOverlap` assembles the normalized
torus components over the actual double overlap. The exact component
formula and inclusion square are proved using the published finite
component assembly and `semilinearComponent_naturality`.
`galoisTorusDatum` proves the cocycle by cancellation of the closed torus
inclusion into the ambient datum, and `compatible_galoisTorusDatum`
records the compatibility needed for effective descent.

The provenance is an internal derivation from the imported actual
semilinear pinning, finite-component descent, and closed-subgroup
cocycle constructions. No finite field, cyclic action, effective
solution, or comparison with an absolute star action is asserted here.
