# Isomorphisms on the coproduct of an étale cover

Worker 812. This internal construction uses the full natural Isom sheaf, the
actual scheme coproduct, and the published all-test correspondence with
pullback group-scheme isomorphisms. It cites no new literature theorem.

Full natural Isom families agree on a relative test with initial underlying
scheme, because every further test mapping to it is also initial. Arbitrary
families on the components of a scheme coproduct are therefore compatible:
two maps into different components with equal composites force the test
scheme to be initial, by disjointness of scheme coproducts; maps into the
same component agree by its monomorphism.

The coproduct component inclusions form a Zariski cover, hence an fppf
cover. The full Isom sheaf glues the compatible families to
`LocalGroupIso.sigmaFamily`, whose restriction to each component is the
original family.

`LocalGroupIso.isoOnSigma` converts actual isomorphisms of the two group
pullbacks over each member of an étale covering family into natural families,
glues them over the scheme coproduct, and converts back to an actual
group-scheme isomorphism there. The coproduct base map is the actual
`Sigma.desc` of the cover maps. No finiteness or nonemptiness condition is
imposed on the indexing type.
