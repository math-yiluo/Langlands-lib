# From ambient Čech boundary lifts to actual adic cohomology kernels

This internal reduction connects a boundary-lifting estimate in the ambient
Čech complex to the actual ideal-multiple sheaves and quotient cohomology.
It uses the actual inclusions and transition maps from `IdealAdicQuotients`,
the affine range results from `IdealAdicMultipleFiniteSections`, and the
natural Čech comparison from `CechResolution.Naturality`. The uniform
boundary-lifting estimate remains a hypothesis. The proposition definition
`CechBoundaryLift f M 𝒰 I J p` names that estimate: every ambient
degree-`p` cochain whose boundary is in `I` times degree-`p+1` cochains
has a cochain in `J` times degree-`p` cochains with the same boundary.

For any finite ordered affine cover, `cochainMap_inclusion_eq` identifies
the map induced by the actual inclusion with `inclusionFamilySections`.
Consequently `cochainMap_inclusion_injective` is unconditional. If the
structural morphism is separated, the module is quasi-coherent and the
ideal is finitely generated, `range_cochainMap_inclusion` identifies its
range in each degree with the ideal multiple of the ambient cochain
module. All nonempty finite intersections in this cover are affine.

For finitely generated ideals `I ≤ J`, fix degree `p`. Assume that every
ambient degree-`p` cochain whose boundary belongs to `I` times degree-`p+1`
cochains has another cochain in `J` times degree-`p` cochains with the same
boundary. Then `ker_inclusion_le_of_cech_boundary_lift` proves that the
kernel of the map from `H^(p+1)(IM)` to `H^(p+1)(M)` is contained in the
kernel of its map to `H^(p+1)(JM)`.

The proof first uses quasi-coherence of both actual ideal multiples,
then applies `ker_relativeCohomology_map_le`. A coboundary in the ambient
complex lies in `I` times cochains because it is the image of a cochain
of `IM`. The assumed estimate supplies a cochain in `J` times cochains
with that boundary. The affine range result lifts it to a cochain of
`JM`. Naturality of the differential and injectivity of the inclusion
show that its boundary is the transition image of the original cochain.
This satisfies the criterion for the claimed inclusion of cohomology
kernels.

Finally `adic_stable_image_of_cech_boundary_lift` assumes the ambient
estimate simultaneously for `I^k` and `I^n` whenever `n+c ≤ k`, with a
single supplied `c`. Over a noetherian ring both powers are finitely
generated. The preceding kernel result and the long-exact-sequence
reduction give the equality of the actual quotient-transition and
projection ranges, with exactly the same bound and quantifiers.

This is a derivation from the imported interfaces and elementary diagram
identities. It proves no existence of a boundary-lifting bound from
properness or coherent finiteness, and therefore does not by itself
prove `ProperAdicCohomologyStableImageStatement`. No local-ring,
completeness, flatness or projectivity hypothesis is used.
