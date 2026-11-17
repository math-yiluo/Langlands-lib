# Based global isomorphisms from coherent actual root frames

Worker 591, using Worker 686's actual chart constructions. This internal
adapter assumes supplied full global coordinate root data, chosen bases
matched by one full root-datum equivalence, coherent actual root frames,
and the exact affine pinned isomorphism theorem.

`datumTorusIso` constructs the coordinate-torus isomorphism determined by
the full character-lattice map. Its base-change law uses the actual
coordinate-torus pullback isomorphisms. Its character formula holds on
every relative test scheme and every integral character.

`globalPinnedIso` specializes the descent construction
`globalIsoOfCoherentFrames` to the scheme's canonical affine open cover.
The cover's disjoint-union map is étale and surjective, hence flat and
locally of finite presentation. The scheme need not be affine,
connected, noetherian or quasi-compact. Exact recovery of the normalized
canonical comparison on each member is stated by
`globalPinnedIso_on_member`.

`affineFrameIsoOver_torus` conjugates the fixed comparison's torus square
by the actual direct/iterated pullback identifications. This proves the
exact torus square for the normalized original-group comparison on any
common scheme. `globalPinnedIso_torus` checks the global square on the
canonical affine neighborhoods using member recovery, the local square,
the torus base-change formula and fppf locality of equality of group
homomorphisms.

When the original base is nonempty,
`pairing_of_globalCoordinateRootDatum` uses an actual residue-field
realization at one point to identify the entire coordinate pairing with
the standard dot product. Consequently `basedIsoOfCoherentFrames`
packages the actual global group isomorphism, the exact torus square,
the specified full based root-datum map and its all-test character law
as `BasedCoordinateIso`. Its existing `range_torus_comp` method proves
transport of the full torus subgroup functor. Its
`range_parabolic_comp` method transports any supplied representatives
of the two canonical based dynamic parabolics.

The frame coherence input has exactly the original-group dual-number
point meaning of `AffineRootFrames.IsCoherent`. This module does not
construct frames from a Picard hypothesis, select bases from supplied
Borels, produce the root-datum map from local group isomorphisms, or
prove the affine pinned theorem. Those remain separate obligations for
the parent isomorphism statement.
