# Local generator coherence for determinant pullback

This derived prerequisite concerns actual module sheaves with supplied finite
free frames on open charts of schemes in an arbitrary universe. Every frame
uses the same finite index type. The two frame systems may use different
covers. Covering hypotheses are required for global determinant maps and for
separation by their generators.

`frameGenerator_mapFrames` identifies the actual local generator after a module
isomorphism. `localHomPullback_precomp` and `localHomPullback_postcomp` are the
specializations of actual local-map pullback naturality used here.
`frameGenerator_pullback_id` and `frameGenerator_pullback_comp` prove identity
and composition for the local generators of the constructed pulled-back frames.
They use the published local-map pullback comparisons and the canonical
structure-module comparison, with restricted comparison maps canceled on the
same inverse-image open.

`isoMatrix_eq_one_of_frameGenerator` and `isoUnit_eq_one_of_frameGenerator`
show that a module isomorphism preserving the chosen generators has identity
coordinate matrix and determinant coefficient one. Evaluation at the unit
section reduces the hypothesis to equality of the corresponding frame vectors;
taking coordinates and then determinants gives these conclusions.
`isoMap_hom_app_genSec_of_frameGenerator` applies this coefficient calculation
to the actual determinant map's published generator formula.

`hom_ext_genSec_to` proves that determinant generators determine maps into any
module sheaf: the local generator spans on each chart, and sheaf separation
uses the covering hypothesis. `pullback_hom_ext_genSec` derives the analogous
criterion for maps from the actual pullback by the pullback-pushforward
adjunction. The elementary identity-open and isomorphism-composition evaluation
lemmas make the source and target of section comparisons explicit.
`pullback_identity_of_genSec` gives a conditional equality criterion: any two
comparison isomorphisms whose composite returns all original determinant
generators equal the canonical identity pullback comparison. Its hypothesis is
explicit; this criterion alone does not verify it for determinant pullback.

`pullbackIdentityIso` is the actual determinant map induced by the canonical
module isomorphism from identity pullback to the original module. It is obtained
by `isoMap` from the pulled-back frames to the original frames.
`isoUnit_pullback_id` proves that its local determinant coefficient is one,
using the local generator identity. `isoMap_pullback_id_genSec` proves that this
map preserves the corresponding local determinant generators.

These are derived constructions and proofs from the actual free-frame,
local-map, cocycle, and determinant APIs. The module does not establish the full
identity or composition equality for the global determinant pullback
comparison, compatibility with changes of covers, varying-rank determinants,
or a parabolic Lie determinant or its ampleness. Those remain separate steps
in the smooth proper representability task.
