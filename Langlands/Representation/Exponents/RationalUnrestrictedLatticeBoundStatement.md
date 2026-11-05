# Unrestricted coefficient growth on rational uniformizer lattices

`Langlands.Plancherel.RationalUnrestrictedLatticeBoundStatement.{u,uV,uI}` is an
internal intermediate assertion for coefficientwise moderate growth on actual
rational points. It retains the explicit premise
`SimultaneousStandardBasisAt i ν K0` for a supplied subgroup `K0`.

For a connected reductive group over any nonarchimedean local field and an
actual maximal split torus, take a finite family of cocharacters whose
simple-root pairings are nonnegative. For every admissible smooth complex
representation, smooth dual functional and vector, the conclusion bounds the
coefficient on all nonnegative integral combinations of these cocharacters by
a positive constant times a product of positive coordinate powers. The same
bound is uniform over two supplied compact outer translates and a finite
middle translate. The lattice map is the actual `uniformizerPowers i`, and the
topology is the canonical `rationalPointTopology`.

This includes cocharacters on walls, central directions, empty coordinate
types and relative rank zero. It assumes neither strict exponents nor finite
length, and the representation-carrier universe is independent of the field
universe. No extra local-compactness premise is added to the rational-point
group. The chosen basis is an actual hypothesis; this assertion proves
neither its existence nor any Cartan decomposition or polynomial comparison
with `rationalMatrixNorm`.

The provenance is internal and derived. The intended route is unrestricted
finite-dimensional compression on the small fixing subgroups supplied by the
basis, followed by the finite-orbit compact-translate bound. The published
chamber and compatibility lemmas identify the conjugation data for weakly
dominant actual uniformizer powers. No claim is made that this intermediate
conditional assertion is the full statement of Waldspurger I.4.4.
