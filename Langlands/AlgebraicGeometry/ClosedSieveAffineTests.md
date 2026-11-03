# Closed sieves detected by affine tests

This internal helper extends affine-source criteria for a sieve to all source
schemes, then glues closed representatives over affine opens of the target.
It reuses the published subcanonical lifting lemma
`FppfClosedLocusDescent.exists_lift_of_covering` and the published theorem
`closedLocusFromAffineCharts`. No literature statement is attributed to this
particular interface.

`AffineTestRepresents E ι` says that factorization through the actual morphism
`ι` is equivalent to membership in `E` for every affine source scheme.
`allTests_of_affineTests` proves the same equivalence for every scheme when
`ι` is a monomorphism, `E` is closed for a subcanonical topology `J`, and `J`
contains the Zariski topology. In one direction, factorization gives sieve
membership on an affine open cover, hence globally by closedness. In the
other, membership gives unique local lifts on that cover; subcanonicity glues
those lifts through the monomorphism. The cover need not be finite.

`glue` assumes a closed immersion representing the pullback sieve on affine
tests over each affine open of the target. It applies the preceding theorem
to extend each chart to all tests. Closedness of the sieve also makes its
property local on preimages of target affine opens, since those preimages
form a Zariski cover. The imported chart-gluing theorem then constructs a
single closed immersion representing `E` on all scheme tests. This helper
retains arbitrary universe `u` and imposes no finite-generation, finite-type,
reducedness, or Noetherian assumption.
