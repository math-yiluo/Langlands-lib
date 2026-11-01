# The group-labelled small-etale site

This internal extension of `EtaleTransportCategory` uses a scheme `Y` in
universe `u`, a group `G` in an independent universe `w`, and an actual
action `ρ : G →* (Aut Y)ᵐᵒᵖ`. It defines covers and sheaves on the category
of genuine group-labelled semilinear scheme maps, without imposing
topology, faithfulness or finiteness on the group.

`inclusionSieve ρ S` pulls a sieve back along the ordinary small-etale
inclusion. `transportTopology ρ` declares `S` covering precisely when this
ordinary sieve covers in `Y.smallEtaleTopology`. The maximal-sieve axiom
is the ordinary one. For pullback stability, factor a labelled arrow
through its translated source and ordinary part. Pull the ordinary
cover back along the ordinary part, and then use cocontinuity of
`EtaleAutomorphism.siteMap` to pull it back to the original source.
Precomposition by each source translation carries the resulting
ordinary arrows into the required transport pullback sieve. Equality
is checked in both the group label and the actual scheme map.
Transitivity follows from ordinary transitivity and the formula for
commuting functor pullback with sieve pullback.

`mem_transportTopology_iff` states the defining ordinary-sieve criterion.
`mem_transportTopology_iff_ordinary` expands this into point lifting by
ordinary arrows. `mem_transportTopology_iff_points` shows equivalently
that the underlying scheme maps of all arrows in `S` jointly cover
the target's points. For the converse, undo each arrow's translation
to obtain its ordinary part in the sieve; its underlying scheme map
is unchanged.

`inclusion_coverPreserving` follows because each ordinary covering
sieve is contained in the pullback of its pushforward.
`inclusion_compatiblePreserving` proves preservation of compatible
families for every universe of type-valued sheaves. Two transport maps
with equal composites along ordinary arrows have the same label.
Their ordinary parts therefore have the same translated source, and
their ordinary composites are equal as scheme maps. Ordinary
compatibility followed by restriction along the common translation
proves the desired equality. These results give `inclusion_isContinuous`.

`isSheaf_of_isSheaf_inclusion` constructs descent on any transport
cover from ordinary descent. First amalgamate the label-one family.
For an arbitrary arrow of the covering sieve, use its ordinary part
and canonical translation factorization to check the amalgamation
equation. Ordinary uniqueness gives uniqueness. Applying this
type-valued statement to each coyoneda proves
`isSheaf_transportTopology_iff` for any coefficient category `A`, with
independent object and morphism universes.

`EtaleTransport.Sheaf ρ A` is Mathlib's actual category of sheaves on
this site. Objects are presheaves on the group-labelled category
satisfying the proved sheaf condition; morphisms are natural
transformations, and thus commute with every labelled restriction.
`toSheaf ρ A` is restriction to the ordinary small-etale site; its
underlying-presheaf formula is `toSheaf_obj_obj`.

The ordinary topological transport-site construction in
`Langlands.Sheaf.Equivariant.Site` supplies the proof method for
compatible families and descent. Here the argument uses actual
semilinear scheme maps, ordinary-part maps, equality of their scheme
composites and automorphism-site cocontinuity.

This is an internal construction from the existing transport category,
ordinary small-etale topology and automorphism-site cocontinuity, not
a new literature assertion. No desired cohomology object or comparison
is assumed. Comparison with the earlier translation-data presentation,
abelian and injective structures, derived representation-valued
sections, group smoothness, supports, analytic geometry and Harris
arithmetic specialization remain separate obligations.
