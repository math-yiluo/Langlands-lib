# Assembling coordinate-torus conjugators over affine open covers

This internal derived module assembles actual affine-open-chart conjugators
and proves the isogeny-torus rigidity proposition conditional on the explicit
`AffineSplitSurjectionRootDatumStatement`. That intrinsic compatibility
proposition remains an assumption throughout the final reduction.

`HasAffineOpenCoordinateTorusConjugacy` is a Prop-valued predicate for two
homomorphisms of group schemes over an arbitrary scheme and a target
coordinate-torus inclusion. It supplies an actual affine open cover. On each
chart the two canonical pullback homomorphisms admit an fppf local conjugator
in the coordinate torus, whose inclusion is the pulled-back original
inclusion precomposed with the inverse canonical split-torus isomorphism.
No reductivity, isogeny or affineness hypothesis on the groups is used in
this generic predicate or its descent theorem.

`HasAffineOpenCoordinateTorusConjugacy.fppfLocallyTorusConjugate` regards
the affine open cover as an fppf cover, using flatness and local finite
presentation of each open immersion. It transports each chart's conjugators
from the coordinate torus to the actual pulled-back torus by the canonical
isomorphism, then applies the existing fppf-cover composition theorem. The
result retains all scheme tests in the original conjugacy predicate.

`coordinateSplitIsogenyTorusConjugacy_of_affineSplitSurjectionRootDatum`
proves the coordinate affine conjugacy assertion for every commutative ring,
using that intrinsic proposition. The source and target are reductive,
their coordinate tori are closed and fibrewise maximal, their full
fibrewise root data and free actual root-weight lines are supplied, and
both ambient homomorphisms are isogenies with the same torus restriction.
No root-datum isogeny or character map is supplied as an extra premise.

The proof regards the supplied torus homomorphism as a homomorphism of
commutative group schemes. The intrinsic proposition and the existing
neighbourhood-character adapter yield an actual affine open cover on
which one root-datum isogeny and one torus character map serve both
ambient homomorphisms. Each chart retains reductivity, finite ambient
maps, closed fibrewise maximal coordinate tori, the same full fibrewise
root data, and free actual root-weight lines by the affine transport
lemmas. The supplied-root conjugacy theorem gives fppf local all-test
conjugators on each chart. The generic cover-descent step above composes
these into an fppf conjugating cover of the original affine base.

`reductiveIsogenyTorusRigidity_of_affineSplitSurjectionRootDatum`
composes this coordinate result with the existing coordinate-to-general-base
reduction. Its conclusion is the unchanged
`ReductiveIsogenyTorusRigidityStatement` in every universe, still under the
explicit intrinsic compatibility hypothesis. The general-base reduction
includes the reverse implication and uniqueness modulo the scheme-theoretic
centre. This module does not prove the intrinsic proposition and therefore
does not constitute an unconditional proof of the host target.

The provenance is direct composition of the existing neighbourhood-character
cover construction, actual affine root-datum and free-weight transport,
supplied-root conjugator construction, coordinate-torus isomorphism
transport, fppf-cover composition, and the general-base reduction. The cover
step also uses the flatness and local finite-presentation instances for
open immersions. No additional source theorem is asserted.
