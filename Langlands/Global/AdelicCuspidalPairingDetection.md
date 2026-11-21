# Vanishing of automorphic forms from their cuspidal pairings

`HasVanishingCuspidalPairings` says that each standard constant term has absolutely
convergent and zero norm-one Levi pairings against every cuspidal automorphic test,
at every ambient adelic translate. The test and measure are the ones used by
`IsCuspidalProjection` in `AdelicLeadingCuspidalComponents`.

`isGlobalLeadingCuspidalComponents_zero_of_pairings` uses zero as a cuspidal projection
of each constant term. Zero is automorphic and cuspidal, and its integrand is identically
zero. The absolute convergence and vanishing in the hypothesis give the remaining
clauses of the projection relation. Its empty exponent decomposition gives a zero
leading component. The same construction supplies zero leading components for the
zero input, whose constant terms vanish.

`eq_zero_of_hasVanishingCuspidalPairings` compares the given global automorphic form
with zero by `LeadingCuspidalInjectivityStatement`, with that statement's compact and
automorphy hypotheses. The injectivity statement is an explicit premise. The proof
directly constructs the zero projections from the pairings, so no existence or
decomposition theorem for arbitrary cuspidal projections is needed.

This is a derived consequence of the pairing characterization and leading-component
injectivity in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
§6.2, (6.8), and §6.3, Theorem 6.3.
