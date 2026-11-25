# The DVR valuative reduction for reductive group monomorphisms

This internal construction applies the published `DvrCase` proposition to actual
base changes of the source and target groups of a monic homomorphism from a
reductive group scheme. The target is separated, locally of finite presentation,
and quasi-compact over the original base.

`hasLift_of_dvrCase` proves that any actual valuative square for this homomorphism,
whose valuation ring is a discrete valuation ring, has a lift. It pulls the groups
back to that ring along the base map defined by the integral target point. The
published reductive base-change theorem retains reductivity. The target
properties and monicity also survive pullback, so `DvrCase` makes the pulled-back
homomorphism a closed immersion. The existence part of the valuative criterion
for universally closed maps then gives a lift in the pullback, and the first
projection gives the lift in the original source.

`dvrValuativeLift` chooses this actual lift, with both factorization equations.
This is derived internal content; it uses the Library's actual group pullbacks
and Mathlib's valuative squares, without translating an external theorem.

`isClosedImmersion_of_dvrCase` assumes that the original base is locally
noetherian. The target is then locally noetherian because its structure morphism
is locally of finite type. The homomorphism itself is locally of finite type,
and is affine because the source is affine over the base and the target is
separated over it. On each affine target chart, the DVR lifts above pass to the
actual pullback square. The published noetherian DVR criterion for universal
closedness applies to that quasi-compact, locally finite type pullback. Universal
closedness is local on the target, so the original homomorphism is universally
closed, hence proper and, by monicity, a closed immersion.

`reductiveMonomorphismValuativeReduction` proves the unchanged published
`ReductiveMonomorphismValuativeReductionStatement.{u}` in every universe:
`DvrCase` is equivalent to `LocallyNoetherianCase`. The reverse direction
specializes to the spectrum of a DVR, which is locally noetherian.

The noetherian DVR criterion is reused from
`Langlands.AlgebraicGeometry.NoetherianValuativeCriterion`; its proof and licensed
dependencies are not reproduced here. This module does not prove `DvrCase`, the
separate approximation to noetherian bases, or the closed-immersion theorem over
all bases (`ReductiveMonomorphismClosedImmersionStatement`).
