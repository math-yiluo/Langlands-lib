# Conductor reduction with the trace character and orbit transport

`CuspidalSigmaLiftConductorFromTraceEpsilonStatement` gives the exact
Library conductor identity from `CuspidalSigmaLiftTraceEpsilonDataStatement`.
The two propositions have the four independent universes of the target.
The local data supply a base character of additive conductor zero and use
the Library trace pullback on the extension. They supply a finite newvector
conductor separately for every twist and orbit block through
`IsStandardEpsilonConductor`. The remaining factor hypotheses are
`OrbitProductEpsilonMultiplicativity` and `EpsilonMonomialProductComparison`.

The Lean proof uses `IsDifferentExponent.additiveConductor_of_trace` to
obtain additive conductor `d` on the extension. Each field automorphism
`σ^i` and its inverse are continuous by the module topology. Applying
`Conductor.isNewvectorConductor_comp_fieldEquiv_iff` to `σ^i` identifies the
newvector level certified for that block with a newvector level for `Π₁`.
The rank equality gives `s > 0`, so the conductor from block zero certifies
a conductor for `Π₁`. Uniqueness of the newvector conductor identifies
all the block values. These data verify the hypotheses of the earlier
local epsilon reduction.

This is an internal consequence of the published conductor, trace, and
sigma-lift definitions and of the local exponent comparison for Arthur
and Clozel, Chapter 1, Proposition 6.9(ii). The factor hypotheses above
are premises of the implication.
