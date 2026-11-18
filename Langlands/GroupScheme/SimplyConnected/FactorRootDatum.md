# Actual factor root indices and integral Cartan pairings

This derived internal comparison uses supplied actual root data of the
ambient split maximal torus and the compatible split maximal torus of one
actual simply connected product factor.

`rootIndex` takes a factor root to the unique ambient root whose actual
character is its pullback along the retained torus projection. `rootIndexEquiv`
identifies all factor root indices with exactly the ambient indices assigned
to that factor by actual root-subgroup containment. Injectivity uses the torus
projection's section; surjectivity uses the full actual root bijection in
`FactorRoots`.

`coroot_projection` shows that the matching ambient coroot maps to the factor
coroot under the actual torus projection. The published coroot-comparison
criterion applies to the projection square: its torus map is epimorphic because
it has the specified section, and the factor's full actual Weyl image is finite.
This criterion does not require the group map to be an isogeny.

`pairing_rootIndex` evaluates a pulled-back root on the projected coroot. It
preserves every ordered integer root-coroot pairing exactly. This module does
not yet assert that an arbitrary chosen factor base is the ambient base's
restriction. The field, characteristic and universe are unrestricted.
