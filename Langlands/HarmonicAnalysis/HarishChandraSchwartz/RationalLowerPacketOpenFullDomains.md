# Lower packet densities on nonempty open full convergence domains

`LowerPacketOpenFullDomains` asks for openness and nonemptiness of both actual
full convergence domains at the literal lower compact. The domains use the
conjugated inducing representation and the cocharacter in the actual smaller
Levi. The field and representation carrier have independent universes.

When the output face is empty, its standard Levi is the centralizer of the
maximal split torus. The conjugated cocharacter inside this Levi factors
through that torus. Centralizer restriction along the monic Levi inclusion
shows that its centralizer is the entire lower Levi. The published full-Levi
results give universal forward and reverse domains.

`exists_lowerDensityPackage_at_compact_of_openFullDomains` uses the transported
split component of the lower parameter scheme and the actual compact Iwasawa
factorizations. Irreducibility gives finite length of the conjugated
representation. The two published open-full-domain constructors then give
`ForwardContinuation` and `ReverseContinuation`, using the original lower
intertwining measures. `lowerDensityFromOppositeContinuations` constructs the
density with the transported split-central quotient Haar and square integrability.
The output compact is the literal intersection with the ambient compact.

This derived step supplies the lower density input in Waldspurger's VI.3.1
rank-induction argument, printed p. 304 in the registered source
`waldspurger-2003-plancherel`. The convergence conditions are explicit for
general output faces.
