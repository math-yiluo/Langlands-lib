# Embeddings of an actual star vertex field

Let `K` be a field and let `d : TitsIndexData G` be actual index data for
an affine locally finite type group scheme `G` over `Spec K`.

`starVertexNormalClosure` takes the normal closure of the actual simple
vertex field inside the original separable closure. For each embedding of
the vertex field into that finite Galois extension, `starVertexEmbeddingLift`
extends it to an automorphism of the original separable closure.

Two absolute Galois automorphisms give the same star translate of a vertex
exactly when their quotient fixes its actual vertex field. This identifies
the embeddings into the normal closure with the vertices in the full star
orbit. Every translate is attained because restriction of its automorphism
to the vertex field factors through the normal closure. The degree formula
for the vertex field therefore counts its embeddings into this extension.

Assume `hsc : IsSimplyConnected G` for the weight identity. The full
simple-coroot span supplied by this hypothesis gives integral fundamental
characters in the character lattice of the absolute torus. The star action
carries each such character to the one at the translated vertex. Summing
over the finite embedding set under the proved bijection gives
`d.absoluteOrbitWeight hsc a`, with one term for each vertex in the orbit
of `a`.

This internal construction uses the published vertex-field stabilizer and
degree comparisons and the normal-closure construction. It works for
nonnormal vertex fields and in every characteristic.
