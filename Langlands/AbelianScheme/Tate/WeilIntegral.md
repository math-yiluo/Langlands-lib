# The actual integral Weil pairing, conditional on relative compatibility

This internal construction transports the published `finiteWeilBilinearMap`
through `GroupScheme.Tate.kernelLevelEquiv` and `mu.pointsLevelEquiv`, then takes
coherent families. These identify the actual torsion-scheme points with the
torsion-section levels and the actual roots-of-unity points with the roots in
the global sections of the test scheme. The relative transition theorem is an
explicit argument, `RelativeFiniteWeilTransitionStatement`. Its truth is not
established by this file.

The input is an actual abelian scheme on a quasi-separated scheme, the exact
chosen dual construction, the seven tensor/Picard prerequisites, and the actual
inverse Poincare line bundle with evaluation. No arbitrary pairing is supplied.
The value retains `beta(y)(x)`. The target consists of actual roots of unity in
the ring of global sections of the test scheme.

`finiteWeilLevelBilinearMap` is this transport at every natural order, including
zero. Its `_apply` lemma identifies its value with the original
`finiteWeilPairing` evaluated at the actual kernel lifts. The `_transition`
lemma uses positive orders. Its proof evaluates the assumed scheme-map
equation on the pair of actual kernel points, rewrites composition with the
product map, and applies `mu.pointsLevelEquiv_transition`.

`integralWeilValue` evaluates each pair of coordinates using that transported
finite pairing. Coherence follows from `_transition` and the two input
coherence equations. `evaluation_integralWeilValue` gives the defining
coordinate formula. `integralWeilBilinearMap` bundles this same value as a
bilinear map over `Global.ProfiniteIntegerRing`; its `_apply` lemma is
definitional. Additivity is checked coordinatewise. Scalar compatibility uses
`ZMod.map_smul` for the additive finite pairing and the existing residue
actions.

The predicate selecting positive orders is arbitrary, so taking it to be
`True` gives the full pairing. Taking it to be `Nat.Coprime · p` gives the
prime-to-p value. `awayWeilBilinearMap` bundles this latter value over
`Global.PrimeToProfiniteIntegerRing p`, using the existing away residue
actions. Its `_apply` lemma identifies its value with that same selected
pairing. The definition works for any natural `p`; primality is not needed
for the restriction construction. `restrictAway_integralWeilValue` proves
that restricting the full twist value equals pairing the restrictions of
the two inputs.

`integralWeilValue_unique` proves uniqueness among functions with the displayed
coordinate formula by equality of all coordinates. Joint continuity in
`continuous_integralWeilValue` follows from continuity of each input
evaluation and the discrete topology on each torsion level, followed by the
product and subspace topology constructions. A private lemma carries out the
discrete-level argument for arbitrary commutative group objects. Finiteness
of these levels is not needed.

The provenance is the internal derivation just described from the published
finite pairing, kernel and roots-of-unity equivalences, and inverse-limit
scalar APIs; no external theorem is newly generalized here. No finite
etaleness, rank, perfectness, alternation, monodromy equivariance, prime-adic
or rational pairing is claimed. No roots of unity or basis of the twist
are chosen.
