# The local smooth-DVR affinization construction

Worker 596, using Worker 183's principal-open and translation constructions.

Over a Henselian DVR with separably closed residue field, let `G` be an
actual smooth, quasi-compact, separated group with affine actual generic
fibre. Supply an actual compatible group law on its prescribed canonical
affinization, and a fibre-dense affine open `W` (density is needed only in
the closed fibre). `canonicalIso` constructs the actual canonical
isomorphism `G → Spec Γ(G,O_G)`, and `isAffineHom` concludes relative
affineness. The forward map is precisely `Scheme.toSpecΓ`.

These are two explicit construction inputs, still to be supplied by the
independent prerequisite tasks. This module does not claim the unconditional
smooth-DVR affineness theorem.

## Implemented proof and provenance

First, flat affine base change of global functions constructs
`baseChangeSpecIso`; its exact projection formulas identify the
base-changed canonical map with the canonical map of the source base
change. An affine generic fibre thus makes the actual generic canonical
map an isomorphism.

The supplied affine open and Worker 183's BLR principal-function
construction give a smooth source chart for the canonical map that meets
the special fibre. The source group has such a fibre point from its unit.
Henselian lifting and density of rational points over the separably closed
residue field propagate smoothness by translations. The generic
monomorphism criterion, using smoothness and separatedness of the source,
then makes the total canonical map an open immersion.

Finally, the canonical map is bijective on global functions. The direct
`DvrOpenAffinization.isoOfGeneric` construction makes it an isomorphism:
the special-fibre image is closed by the arbitrary-field open-subgroup
lemma and dense by the actual section embedding, so is surjective; the
generic and closed fibres then give total surjectivity.

This is an internal assembly of the named constructions and the existing
flat-base-change theorem. It retains arbitrary characteristics and
possibly disconnected groups. The affine target is not assumed to be of
finite type, smooth, or to have reduced special fibre.
