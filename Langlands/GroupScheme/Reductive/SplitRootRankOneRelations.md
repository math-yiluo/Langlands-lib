# Rank-one relations for every root of a supplied split root datum

This internal derived unit constructs linked additive maps for each root of
an actual supplied split maximal torus and root datum in a connected reductive
group over an arbitrary field. It retains the supplied torus and root datum;
it asserts no existence theorem for these data.

`HasRootRankOneRelations i P` is a proposition requiring, for each root index
`r`, two actual homomorphisms from the additive group to the original group.
The torus acts through `P.root r` and its negative, respectively. For every
relative test scheme the maps satisfy the literal rank-one relation

`xp(a) xm(b) = xm(b') (P.coroot r)(u) xp(a')`,

where `u = 1 + ab` is a unit, `a' = u⁻¹a`, and `b' = u⁻¹b`. The torus
inclusion in the middle factor is the original inclusion `i`.

The proof chooses a cocharacter annihilating the given root and having no
independent annihilated roots. Its actual centralizer is connected reductive
by the published dynamic-centralizer theorem. The supplied torus factors
through this centralizer as a split maximal torus, whose root datum is the
restriction of the original one to the annihilated roots. All its roots are
pairwise dependent. The published `splitRankOneRootCell` theorem therefore
constructs linked additive maps there. Composing with the actual closed
centralizer inclusion preserves both full-torus conjugation laws and the
rank-one relation over every test scheme.

The helper `RootCell.RelationOver.map` explicitly proves preservation of the
relation by a homomorphism compatible with the common torus. The scalar
equivariance helper identifies the weight-point action on a scalar additive
point with multiplication by the character value. The final theorem applies
the construction to any supplied split pinning.

The provenance is internal and derived from existing Library root isolation,
centralizer root data, and the proved semisimple-rank-one root-cell theorem.
The local cell is used only inside the centralizer; the result does not
assert that the three-factor map is open in the arbitrary-rank original
group. It also does not identify these chosen parameters with a supplied
normalized simple-root parameter, prove simultaneous full-unipotent
coefficient nonvanishing, or prove the full Steinberg statement.
