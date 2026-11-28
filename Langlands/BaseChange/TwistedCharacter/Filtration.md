# Twisted distributions on finite invariant filtrations

`TwistedDistributionFiltrationAdditivity` concerns an admissible complex
representation of a locally compact Hausdorff totally disconnected group,
with its Borel structure and a supplied left-invariant measure finite on
compact sets. For a finite `ObjectRepFiltration` preserved by a linear
endomorphism, its twisted distribution is the sum of the twisted
distributions on the successive quotients. The operator on each quotient
is induced by the given endomorphism.

The proof restricts the operator to each invariant subspace and descends
it through the canonical quotient map. The subspaces inherit
admissibility, and compact open averaging gives admissibility of their
successive quotients. The inclusion and quotient map commute with the
operators, so `twistedDistribution_shortExact` gives additivity at each
step. The bottom step gives zero and the top step gives the original
trace by equivariant transport. Summing the step identities gives the
formula, including the empty filtration.

This is the trace additivity used with the stable support filtration in
Rogawski, *Trace Paley-Wiener theorem in the twisted case* (1988), proof
of Lemma 8.1, printed p. 222. The argument applies to any linear operator
preserving the filtration.
