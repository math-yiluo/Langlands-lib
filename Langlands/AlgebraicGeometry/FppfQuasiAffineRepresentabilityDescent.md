# Fppf descent of quasi-affine representability

This derived internal construction descends representability of an actual fppf
sheaf from a single flat surjective locally finitely presented map between affine
bases. The local representing scheme must be quasi-affine. The resulting scheme
is quasi-affine and represents the original sheaf on all schemes over the base.
`quasiAffineModel` chooses this representing scheme with both properties.

The proof uses the representing equivalence to construct the canonical descent
map on the local scheme, with its diagonal section and cocycle identity, via
`UnramifiedFunctor.CompletionDescent.Points` and `ChartDatum`. Applying the latter
with the identity open immersion gives an effective descended scheme. The
published `FaithfullyFlatQuasiAffineDescent.isQuasiAffine_of_isPullback` proves
that it is quasi-affine.

To identify the descended scheme with the sheaf, the chart-element and
factorization arguments of `CompletionDescent.ChartProperties` are adapted to
the fppf topology. The singleton covering sieve is covering because the maps are
flat, surjective and locally finitely presented. The sheaf condition descends the
universal element, and detects equality after pullback. Compatibility of local
points descends their maps by the effective epimorphism property of the flat
surjective quasi-compact cover. The existing chart monomorphism argument gives
injectivity; factorization gives surjectivity on every test scheme. These
bijections, natural by functoriality, are packaged as `RepresentableBy`.

The auxiliary factorization lemma also assumes quasi-compactness of the base
cover; that condition is automatic for the main theorem because both bases are
affine. No sheaf condition for arbitrary fpqc covers is assumed. The construction
is derived from the cited published modules and introduces no external source
claim or additional axiom.
