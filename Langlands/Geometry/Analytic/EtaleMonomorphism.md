# Étale monomorphisms and their open images

Work over a complete ultrametric normed field, with independent field
and space universes. A surjective étale monomorphism is an isomorphism.
For a strong representative, pass to full recognition and choose an
open finite étale model near a point of the source. Recognized target
charts inside the open image of the model have finite étale preimages
in the model. The corresponding affinoid maps are surjective on points.
They are monomorphisms because their composites with the target chart
inclusions are restrictions of the original monomorphism. The finite
affinoid criterion therefore gives an inverse on each such chart.

Surjectivity gives a quasinet of these target charts. Monicity makes
their inverses agree on overlaps, so they glue to a section. Monicity
then gives the other inverse identity. Isomorphisms of the full
recognition presentations and the localized arrow transport this
conclusion to the given map.

An arbitrary étale monomorphism factors through the open analytic domain
of its range. Étaleness cancels the target domain inclusion, so the
factorization is a surjective étale monomorphism. `etaleMonoImageIso`
is the resulting isomorphism, with the factorization over the original
target. This gives the analytic open immersion property.
