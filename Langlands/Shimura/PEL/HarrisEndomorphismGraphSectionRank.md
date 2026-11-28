# Section ranks of the graph of an endomorphism

On a field test, the graph of the classified endomorphism identifies with the
pullback abelian variety via its first projection. Its two maps to the original
abelian scheme are the pullback projection and the endomorphism followed by
that projection. The affine Hilbert-piece test uses the monoidal power of the
tensor product pulled back along these two maps.

`fibreGraphPowerIso` compares that module after transport along an isomorphism
of fibres that intertwines the endomorphisms. It exchanges the two tensor
factors to use the order \(v^*M\otimes M\). When the pullback of the original
module is isomorphic to \(M^{\otimes q}\), tensor-power distributivity and the
power-of-a-power isomorphism give \((v^*M\otimes M)^{\otimes qk}\) in test
degree \(k\).

`fibreGraphSectionRank_eq_finrank` applies the geometric section-rank
comparison for a cartesian square over the identity of the field. The
identity-field rank formula and the relative global sections comparison
identify the result with the ordinary dimension of sections of this same
line bundle power. This derives the rank comparison from the Library's
Hilbert-fibre and explicit tensor constructions.
