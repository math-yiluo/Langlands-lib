# Finite representatives for irreducible sources

This is an internal finite-length argument for use in the finite-fibre part of
Renard VI.7.1. It follows from the published actual composition-series and
intertwiner APIs. It does not assert any parabolic finite-length, admissibility,
or supercuspidal realization theorem.

`Langlands.SmoothRep.FiniteLengthIrreducibleSourcesStatement` quantifies
independently over the coefficient, group, ambient-carrier and source-carrier
universes. Over a field and a topological group, let `A` be an actual smooth
representation of finite group-algebra length. There are a natural number `n`
and irreducible actual smooth representations `B i`, with carriers in the
chosen source universe, such that every irreducible actual smooth `X` in that
universe admitting a nonzero intertwiner into `A` is isomorphic to some `B i`.
The representatives need not be pairwise nonisomorphic. The list can be empty.
There is no dimension or admissibility hypothesis.

`ObjectRepFiltration.exists_equiv_graded_of_nonzero` first applies the published
`exists_mapToGraded_ne_zero` to a supplied actual composition series. It obtains
a nonzero intertwiner from the irreducible source to one actual graded
quotient. Irreducibility of the source makes this map injective, and
irreducibility of the graded quotient makes it surjective. Its actual
equivariant linear equivalence retains the independent carrier universes.
This helper only needs a monoid.

`SmoothRep.finiteLengthIrreducibleSources` proves the proposition. The published
`MultiplicityAdditivityProof.exists_series` supplies an actual finite
composition series for `A`. From its finite index set, the proof selects exactly
the factors admitting an irreducible smooth representative in the chosen
source universe, and chooses one such representative for each selected factor.
The helper shows that every source under consideration reaches a selected
factor. Composing the two equivalences through that factor gives the required
categorical isomorphism. `Fintype.equivFin` enumerates the selected finite set.

Selecting only factors with a representative in the chosen source universe is
essential: the proof does not resize every quotient of the ambient object.
Neither a smallness assumption nor a universe equality is used.
