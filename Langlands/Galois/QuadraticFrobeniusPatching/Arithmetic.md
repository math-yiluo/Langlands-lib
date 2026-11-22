# Transport of Euler polynomials among number fields

This module specializes the local Frobenius comparison to the completion map
for a place \(w\) of \(E\) above a place \(v\) of \(K\). The map is finite,
commutes with the number-field embeddings, and preserves and reflects the
integer rings. The residue cardinalities satisfy \(q_w=q_v^{f(w/v)}\), where
the residue degree is `w.asIdeal.inertiaDeg (𝓞 K)`. If `Q` has degree equal to
the representation's rank, equality of reversed polynomials at \(v\) gives
equality of characteristic polynomials. The local power formula and
`charpoly_pow` then give unramified Euler matching at \(w\) with the reverse of
`frobeniusRootPower (w.asIdeal.inertiaDeg (𝓞 K)) Q`. [Local Frobenius comparison](Local.md), [polynomial identities](Polynomial.md)

For an extension tower \(F\subset K\subset E\), the inverse image of the given
cofinite set of \(F\)-places under place contraction is cofinite in \(E\).
At each such place \(z\), contraction is compatible with the intermediate
place in \(K\). The residue degrees multiply, so the two successive
root-power operations give the exponent \(f(z/v)\) over the single contracted
place \(v\) in \(F\). This lemma applies to the cofinite hypothesis of one
auxiliary field at a time.

An \(F\)-automorphism of \(K\) transports the completion at the corresponding
place to the completion at the original place by a ring isomorphism. Both
places lie over the same place of \(F\) and have the same residue degree over
it. The completion square and the local power formula with exponent one
give the matching assertion for the automorphism pullback.

At a completely split place, the specified completion degree one makes the
completion map bijective. The product formula for the completion degree also
gives residue degree one. The local descent lemma then recovers both
unramifiedness and the given Euler polynomial at the base place.
