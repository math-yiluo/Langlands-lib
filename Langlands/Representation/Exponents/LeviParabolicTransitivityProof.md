# Transitivity for represented parabolics

Authors: Worker 1754 and Worker 1373.

This module proves the published
`Langlands.Aubert.General.RepresentedParabolic.LeviParabolicTransitivityStatement`
without adding hypotheses. Its theorem is `leviParabolicTransitivity`, with the
same independent universes `u` and `v`.

For the original three supplied actual parabolic triples, the structural proof
`nestedParabolicPointDecomposition` identifies the supplied inner radical with
the intersection of the larger Levi and the original radical. It also proves
the ordered product of that intersection with the larger radical equals the
original radical. The proof supplies these two derived identities to
`leviParabolicTransitivity_of_radical_decomposition`.

That adapter constructs the normalized induction and Jacquet natural
isomorphisms for the published functors, using the canonical Levi-point
equivalences, topologies and instances. It proves the half-modulus product and
the coherence of the coefficient-group identifications before transporting
the generic functor comparisons. The unconditional theorem retains the exact
published field, topology, local compactness, nonarchimedean-group, reductivity,
actual-triple and point-image quantifiers. No standardness, chosen cocharacters,
representation finiteness or additional structural premise is imposed.

The source is Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, VI.1.4, printed pages 136–137, PDF pages 142–143.
The implementation derives the needed algebraic structure from rational-point
density and the supplied geometric radicals, then applies the constructed
functor adapter; it does not require a chosen semistandard presentation.
