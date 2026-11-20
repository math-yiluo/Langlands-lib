# Reduction to geometrically connected fibres

`NoetherianAffineConnectedTorusSubgroupRepresentabilityStatement.{u}` is the
noetherian affine representability premise with geometrically connected
ambient fibres. The theorem
`noetherianAffineTorusSubgroupRepresentability_of_connected` removes the
connectedness restriction for smooth separated quasi-compact groups with
affine residue fibres.

The relative identity component has a smooth geometrically connected structure
map. It is quasi-compact over the noetherian affine base since its total space
is open in the noetherian ambient group. On each residue fibre its inclusion
is closed, so the fibre is affine. Every relative torus map factors through
the identity component because the residue fibres of the torus are connected
and the map sends their units to the ambient units.

Compose the supplied universal inclusion with the identity-component
inclusion. The composite stays monic, and the parameter scheme is locally
noetherian. Over any discrete valuation ring such a group with affine residue
fibres becomes affine. The monomorphic torus map over that ring is therefore
closed by the multiplicative-type closedness theorem. The noetherian discrete
valuative criterion proves closedness of the composite. For any test, an actual
closed torus in the original ambient group factors as an actual closed torus
inside the identity component. Naturality of the pullback comparison and
monicity of the ambient inclusion preserve and reflect literal equality of
all-test subgroup evaluations.

The reduction follows the first step of the proof of Raynaud, SGA 3,
Exposé XV, Theorem 8.9(a), Gille–Polo recomposition, PDF p. 62. The closedness
argument uses the affine-residue-fibre assumptions of Corollary 8.11, PDF p. 63,
and the Library's discrete valuative criterion.
