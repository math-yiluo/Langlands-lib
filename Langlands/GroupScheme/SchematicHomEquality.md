# Equality after schematically dense base change

Worker 890.

This internal module derives equality tests and a closedness result from
Mathlib's scheme-theoretic dominance and closed-immersion APIs, the
published reduced induced closed subscheme, and the open equality-locus
helpers. It does not assume reducedness of the source group scheme.

`over_hom_ext` proves that two morphisms into a separated scheme over a base
agree if they agree after a schematically dominant morphism to their source.
The equalizer is a closed immersion. The restriction morphism factors
through this equalizer, so the equalizer's ideal is contained in the
restriction's zero kernel. The equalizer is therefore an isomorphism and
its universal equality implies the asserted equality.

`baseChange_hom_ext` applies this to group-scheme homomorphisms with flat
source and separated target. A quasi-compact schematically dominant base
change stays schematically dominant after pullback through the flat
source. Equality of the pulled-back homomorphisms implies equality after
the projection, and `over_hom_ext` then applies.

`hom_ext_of_dense_open` specializes to a quasi-compact dense open in a
reduced base. The base is reduced, while the flat group scheme above it
may have nonreduced fibres.

`fibre_eq_on_closure_of_open_eq` assumes that the underlying space of the
base is Noetherian. It takes an open where two homomorphisms agree and
proves equality on every residue-field fibre over its closure. Equip that
closure with its reduced induced closed scheme structure. The inverse
image of the given open is dense and is quasi-compact by the Noetherian
space assumption. Pull back the equality to this dense open and apply
`hom_ext_of_dense_open` over the reduced closure. The residue-field
morphism at a point of the closure factors through the reduced induced
closed subscheme, giving the desired fibre equality.

`isClosed_fibre_eq_set_of_locally_eq` additionally assumes that every
fibre equality extends to an open neighborhood. The open equality-locus
helper supplies one open containing exactly the equality fibres and
equality over that open. The preceding closure result makes this open
closed.

`clopenLocus` constructs the resulting subset as an actual `Clopens S`.
`mem_clopenLocus_iff` identifies its points with equality of the
residue-field fibres, and `eq_on_clopenLocus` proves equality after
restriction to its associated open subscheme.

The closure, closedness and clopen-locus results require `NoetherianSpace S`. They do not claim
closedness over an arbitrary base, and this module does not prove the
local extension hypothesis.
