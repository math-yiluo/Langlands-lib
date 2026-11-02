# Weyl-conjugate standard Levis and conditional conjugation assembly

This internal construction defines the conjugate of an actual standard Levi
by an actual relative Weyl element. Its supporting theorems reduce the exact
general `StandardLeviConjugationStatement` either to the existence clause of
`StandardCocharacterStatement` or to `RelativeRootSystemStatement`. The
unconditional general statement remains unproved. All structural premises
of these reductions are explicit.

`standardLeviWeylConjugate i ν J w` is a subgroup functor on every test
scheme. It specializes the published `relativeWeylConjugateSubgroupFunctor`
to `standardLevi i ν J`, using
`torusCentralizer_le_standardLevi`. Thus it is independent of the
normalizer lift for every character subset, without a root-system premise.
`standardLeviWeylConjugate_mk` computes it as the preimage of the standard
Levi under the inverse inner automorphism of a lift. Under explicit
simple-root finiteness and standard-cocharacter existence for `J` and
`J'`, `standardLeviWeylConjugate_eq_of_rootSubset_image` identifies the
conjugate of `J'` with the standard Levi for `J`. Its root-transport
hypothesis is the exact encoded-root-set condition of the public target.
The proof substitutes the published preimage equality and cancels the
inner isomorphism using `SubgroupFunctor.comap_comp`.

`standardLevi_eq_comap_of_standardCocharacter_exists` assumes a standard
cocharacter exists for every subset of the actual simple roots.
`finite_simpleRelativeRoots_of_standardCocharacter_exists` in
`StandardCocharacterFiniteness` supplies finiteness from splitness.
Existence for `J` and `J'` supplies the other two inputs to
`standardLevi_eq_comap_of_rootSubset_image` in
`StandardLeviAnnihilatorTransport`. This gives the exact first conjugation
clause, with the public target's sets of encoded individual roots in the
rational root span and equality on every test scheme.

`standardLevi_eq_comap_of_linearIndependent_simpleRelativeRoots`
needs only independence over the rationals of the rationalized actual
simple roots, together with splitness of the torus. The published
`exists_standardCocharacter_of_linearIndependent` provides the existence
premise for every face; the preceding all-face theorem then gives
conjugation. Independence remains an explicit hypothesis and is not
deduced from connected reductivity here.

`standardLeviConjugationStatement_of_standardCocharacterStatement`
has type `StandardCocharacterStatement.{u} →
StandardLeviConjugationStatement.{u}`. It takes only the existence
conjunct of its premise for each face. The first target conjunct follows
from the preceding reduction. The second uses
`standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq` in
`StandardLeviLiftIndependence`, which imposes no root-transport condition
and applies even when a conjugate image is not a standard Levi. The
conclusion retains the universe `u`, arbitrary fields, the actual
normalizer/full-centralizer quotient and every test scheme. Empty root
sets and subsets remain valid.

`standardLeviConjugationStatement_of_relativeRootSystemStatement` instead
has type `RelativeRootSystemStatement.{u} →
StandardLeviConjugationStatement.{u}`. For the given connected reductive
group and maximal split torus, its premise supplies the actual
`HasRelativeRootSystem i` realization. The published `RootFiniteness`
module deduces finiteness of the simple roots. Worker 185's
`HasRelativeRootSystem.exists_standardCocharacter` in
`RelativeRootStandardCocharacter` supplies a standard cocharacter for
every valid subset using splitness and the generic cocharacter.
The exact encoded-root transport theorem gives the first conjunct, and
the same lift-independence theorem gives the second. This route needs
neither the three dynamic comparisons in `StandardCocharacterStatement`
nor the conditional finiteness result in `StandardCocharacterFiniteness`.
The full actual root-system realization remains an explicit premise; this
reduction does not construct it from connected reductivity.

The provenance is internal specialization and assembly of the named
published transport, finiteness and lift-independence lemmas and Worker
185's published interpolation and conditional root-system adapter.
These dependencies are imported by Lean name. The all-face finiteness
route and the underlying lift-independence and annihilator comparisons
were developed in collaboration with Worker 1220. This module supplies
conditional reductions and an unconditional quotient-indexed conjugate
construction; it supplies no unconditional actual root-system realization
or simple-root independence theorem.
