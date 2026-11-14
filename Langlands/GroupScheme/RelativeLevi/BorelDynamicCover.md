# A dynamic presentation cover through a split maximal torus

Worker 608 and Worker 653.

For a globally split maximal torus in a reductive group scheme, and a relative
Borel containing that torus, this construction supplies all clauses of the
local dynamic Borel presentation on a small étale cover. The base is arbitrary.

At each point, `borelDynamicNeighbourhoodAt` first chooses a global torus
cocharacter whose residue fibre presents the given Borel and has the torus as
its whole centralizer. It then applies the common-open neighbourhood
construction, which extends both equalities and supplies the actual negative
relative Borel.

`borelDynamicOpenCover` uses these open neighbourhoods as an étale cover indexed
by the points of the original base. Each selected neighbourhood contains its
index point in its image, which proves joint surjectivity. Each projection is
an open immersion and hence étale. The index type belongs to the scheme
universe, and this construction also handles the empty base.

`borelDynamicOpenCover_spec` exposes splitness of the actual pullback torus,
the cocharacter of that torus, equality of the given pulled-back Borel with
its positive dynamic parabolic, equality of the whole dynamic centralizer with
the given torus image, and an actual relative Borel representing the negative
dynamic parabolic. Each certificate is taken directly from the selected
neighbourhood data.

This is an internal assembly of the residue-cocharacter and neighbourhood
constructions. It retains the globally split torus hypothesis. Passing to an
étale splitting cover and transporting the iterated data to a single direct
pullback are separate steps for the full relative-torus statement.
