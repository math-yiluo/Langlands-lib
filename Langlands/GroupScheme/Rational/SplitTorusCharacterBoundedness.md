# Algebraic bounds from split-torus coordinates

Worker 336. This internal definition and its auxiliary boundedness theorem supply the
Laurent-polynomial step underlying Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*,
Proposition 2.5.8 (printed page 88, PDF page 119). The generic helper is derived content;
it is not a verbatim statement of that proposition.

`splitTorus.unitCoordinateLocus` is the set of rational points of a standard finite split
torus whose actual split coordinates all have valuation one. Over any valuative field,
`splitTorus.isAlgebraicallyBounded_of_unitCoordinates` proves that every set contained
in this locus is algebraically bounded in the regular-function sense.
The implementation writes every point as an evaluation of the actual universal split-torus
point. Every monomial then has valuation one. The subalgebra of uniformly bounded
evaluations is closed under addition and scalar multiplication, so every regular function
has a nonzero uniform valuative bound. The argument uses no compactness or completeness.
