# Periodic automorphisms of compatible left quotients

`PeriodicQuotientAutomorphismPreservation` concerns a closed subgroup `H` of a
locally compact Hausdorff group `G` and the supplied compatible measure `ν` on
`H \ G`. A continuous automorphism of `G` that preserves `H` and has a positive
iterate equal to the identity induces a homeomorphism of `H \ G`. Both that
homeomorphism and its inverse preserve `ν`.

The implemented proof iterates the continuous automorphism and uses
multiplicativity of the Haar modulus. A positive power of the modulus is one,
so the modulus is one. The inclusion of `H` intertwines the restricted and
ambient automorphisms and hence their iterates, giving the same conclusion for
the subgroup modulus. `IsCompatible.map_quotientAutomorphism` then gives
`Measure.map e ν = ν` for the induced homeomorphism `e`. Inverse measure
preservation follows by treating `e` as a measurable equivalence.

This is a measure-theoretic step for carrying the finite-order action through
integration on a Bruhat orbit in the Jacquet calculation of Rogawski,
*Trace Paley-Wiener theorem in the twisted case* (1988), proof of Lemma 8.1,
printed p. 222. The proof uses the general compatible quotient scaling formula.

`iterateEquiv` gives the iterated continuous group isomorphism. `mulEquivHaarChar_iterateEquiv` computes its Haar modulus, and `measurePreserving_of_iterate` gives invariance of every regular Haar measure under a periodic automorphism.
