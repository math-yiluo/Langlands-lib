# Central series with additive factors for unipotent groups

`Langlands.GroupScheme.unipotentAdditiveCentralSeries.{u}` proves
`Langlands.GroupScheme.UnipotentAdditiveCentralSeriesStatement.{u}` for
every universe `u`. The base is an arbitrary field, and the group scheme
has an affine, locally finite type structure map and is unipotent.
[Statement](CentralSeriesStatement.md)

The proof follows Milne's intersection of a unipotent algebraic group
with the central series of the upper unitriangular group. The source is
J. S. Milne, *Algebraic Groups* (2017), Proposition 14.21, printed
pp. 284–285, with Theorem 14.5, §6.49, and Proposition 6.2. The registered
source ID is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The coordinate Hopf algebra has a generating matrix of coefficients with
diagonal entries one and entries below the diagonal zero. The coefficient
homomorphism into `GL_N` is a closed immersion because the entries generate
the algebra. Evaluating those coefficients in the global sections of
each test scheme gives upper unitriangular matrices.
[Hopf coefficients](../../Algebra/GradedHopf/TrivialGrading.md)
[Point evaluation](../Rational/UnipotentCompactSubgroups.md)

The terms of the series are the closed inverse images of the
unitriangular filtration in the faithful representation. The filtration
removes entries one row at a time on consecutive superdiagonals. At a
row with an entry on the current superdiagonal, the additive map is
that entry coordinate, and its kernel gives the next term. A row beyond
the end of the superdiagonal repeats a term and uses the zero additive
map. The series has `N * N` steps, starts at the whole group, and ends at
the trivial subgroup by faithfulness.
[Coordinate series](../Absolute/TriangularCoordinateSeries.md)

For each test scheme, conjugation by a unitriangular matrix preserves the
current superdiagonal layer and fixes its entries. In that layer the
entries of a product add and those of an inverse change sign. The
commutator therefore has zero entries throughout the layer. It lies in
the next full superdiagonal term, which is contained in the next term of
the refined series. These calculations use the original ring of global
sections.
[Superdiagonal filtration](../Absolute/TriangularLayerFiltration.md)
