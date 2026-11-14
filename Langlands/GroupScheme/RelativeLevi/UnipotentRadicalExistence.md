# Constructing relative radicals from etale-local dynamic presentations

This internal construction takes a reductive group scheme `G`, an affine group
scheme `P`, a homomorphism `iP : P ⟶ G`, and an arbitrary etale cover of the base.
On each cover member, the actual pullback of `iP` must represent the dynamic
parabolic of some cocharacter. `DynamicRelativeLeviStatement` remains an explicit
input throughout. The base scheme and universe are arbitrary.

`radical_isMatching_of_etale_dynamicCover` starts with a supplied relative
unipotent radical on each cover member. On a pairwise scheme-theoretic overlap,
both projections are etale, so the radicals pull back with their complete
certificates. The second one is transported into the first pullback ambient
group by the inverse of `CoverDescent.overlapSquareIso`. The local dynamic
presentation on the first member also pulls back. Dynamic radical uniqueness
therefore gives equality of the two subgroup functor ranges on every test
scheme. The overlap matching criterion turns these equalities into
`CoverDescent.IsMatching`.

`radicalOfEtaleDynamicCover` chooses one of the supplied local dynamic
presentations on each cover member and applies `dynamicUnipotentRadical` to
construct the local radicals. The matching theorem just described supplies
their compatibility. `radicalRepresentativeEtale` then constructs an actual
global closed representative with its full `IsRelativeUnipotentRadical`
certificate. The result contains the global group scheme and homomorphism.

The provenance is internal: this composes the dynamic local constructor, etale
transport, overlap comparison, dynamic uniqueness and closed subgroup gluing
interfaces. All subgroup equalities concern arbitrary relative tests, including
nonreduced schemes. This construction does not establish local dynamic
presentations, discharge the dynamic relative Levi statement, or prove the
unconditional global radical statement.
