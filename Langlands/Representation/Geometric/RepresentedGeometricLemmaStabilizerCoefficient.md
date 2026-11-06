# The original full-stabilizer coefficient

This internal adapter concerns arbitrary represented source parabolic data
`P = MN`, with its original rational Levi and geometric unipotent radical,
and any represented target subgroup `Q` and rational point `z`. The field and
ambient point-group assumptions are those available in the published local
orbit-comparison statement. The ambient topology is the canonical rational-point
topology, and the topology on the Levi is `leviPointTopology`. The coefficient
carrier universe remains independent of the field universe.

`parabolicToLeviPoints` is the actual source semidirect projection, transported
from the ambient Levi point image to the Levi's own rational points by
`leviPointsEquiv`. `stabilizerToLeviPoints` composes it with the actual inducing
map on `Geometric.orbitStabilizer P Q z⁻¹`. That inducing map sends `x` to
`z * x * z⁻¹`, so the construction retains the original inverse-representative
convention. Both maps are continuous: the projection has its existing continuity
theorem, the point-image equivalence is a homeomorphism, and fixed conjugation
is continuous in the ambient topological group.

`leviInducingFunctor_eq_twist_comp` identifies the entire original normalized
inducing action with the original source representation, twisted by
`leviInducingHalfCharacter` and pulled back through `parabolicToLeviPoints`.
The proof applies `closedHalfCharacter_eq_comp_projection`. Its unimodularity
premise follows from `isUnimodularModulus_pointImage_radical`, proved in the
Library using the actual radical's compact-subgroup limit property. Thus the
original full-parabolic half-character factors through the Levi projection.
The scalar and the original representation action then agree on every vector.

`stabilizerTwistedCoefficientFunctor` is this half-twist pulled back through
`stabilizerToLeviPoints`. Its objects are smooth because the original character
has open kernel and the stabilizer map is continuous. The natural isomorphism
`stabilizerCoefficientTwistIso` compares it with restriction of the original
normalized coefficient to the full stabilizer. Equality of actions supplies the
identity linear equivalence on each original carrier. Restriction and twisting
preserve the original linear intertwiners, so naturality is equality on every
vector. Applying the actual compact-induction functor gives
`orbitPieceTwistedCoefficientIso`, a natural isomorphism for the original orbit
piece, with exactly the same stabilizer and inverse representative.

The provenance is internal: these constructions combine the published
represented induction, semidirect projection, radical unimodularity and compact
orbit-piece definitions with the original-half character adapter. They do not
use an assumed geometric-lemma comparison. This unit does not identify the
stabilizer's image under the target projection or the source radical image,
integrate over a quotient, or compare distinct radical moduli. The full local
orbit comparison remains open.
