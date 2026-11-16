# Duals of coherent line bundles on presheaves

This internal derived module constructs `PresheafLineBundle.dual` for any
presheaf on schemes over a base `S`. The schemes have universe `u` and the
presheaf values may have an independent universe `v`.

The actual line bundle on each family is the existing internal dual of its
original bundle. For a morphism of families, the cartesian isomorphism first
uses the canonical line-bundle dual-pullback comparison, then dualizes the
original cartesian isomorphism in the same direction.

The identity law follows from the original identity law and dual-pullback
identity coherence. For composition, dualize the original composition law,
move the dual-pullback comparison through the intermediate family isomorphism
using naturality, and use dual-pullback composition coherence. The private
comparison lemma is the same composition equation with the two canonical
pullback isomorphisms moved to the opposite sides by cancellation.

This construction is formal duality infrastructure for coherent line bundles.
It proves no positivity, representability or descent theorem.
