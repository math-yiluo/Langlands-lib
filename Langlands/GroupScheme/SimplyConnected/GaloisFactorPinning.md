# Actual original-field Galois pinnings of recovered geometric factors

This module uses the actual factor root/base/embedding constructions of the modules
`FactorRootBase` and `FactorComponentEmbedding`. Derived from the original-field normal-factor torus, actual reduced root-datum
existence, ambient group-isomorphism transport, and the full orthogonal component
star comparison. The original normal-subgroup model receives a genuine Galois
pinning with its torus and inclusion over the ground field. Its simple vertices
are equivalent to the entire selected ambient simple-root factor fibre; every
ordered Cartan entry and every full star element are preserved. Character
pullback along the original-field torus projection intertwines the ordinary
Galois representations, and the component star lemma removes the Weyl corrections.
The actual subgroup recovery isomorphism and its exact ambient inclusion square
are explicit inputs. No abstract model is substituted for the group.

The vertex permutation `simpleStarVertex` uses `GaloisPinningData.simpleStar` on the support of the chosen base.

`FactorPinningWithProjection` retains the compatible group and torus
retractions from the original construction. Their sections come from
`NormalFactorTorusProjection`. It identifies the group inclusion with the
selected subgroup inclusion and identifies the vertices of the resulting
`FactorProjection` with the ambient vertices in the pinning comparison.
Over the extension field, the published geometric factor root formula
identifies inflation of each simple root with the corresponding ambient
simple root. The original `nonempty_galoisFactorPinning` follows by taking
the pinning comparison from this construction. This extension uses the
same fields, normal subgroup, and recovery isomorphism.
