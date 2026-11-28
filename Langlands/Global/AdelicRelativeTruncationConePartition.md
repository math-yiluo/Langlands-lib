# The truncated negative cone partition in the relative coroot space

The coordinate partition of Delorme, *On the spectral theorem of Langlands*
(2023), §7, equation (7.26), uses the real relative coroot span of a connected
reductive group. Let `I` be the simple roots of the starting standard Levi.
The relative split space is the common root kernel for `I` in the coroot span.
The weights outside `I` are its projected coroot coordinates.

The statement is written after translating by the projection of the base
truncation parameter `T` to that split space. For an increment `S` with
nonnegative simple-root evaluations, the region has upper bounds on the
outside weights of `X − S`. The decomposition `X = Y − Z` has a closed split
term `Y` and a negative Levi term `−Z`, indexed by the unique standard Levi
with simple roots `Q` containing `I`. Outside `Q`, the upper bounds use the
weights of `Y − S`. The outside-`I` coordinates of `Z` are positive on
`Q ∖ I` and zero outside `Q`, specifying the open negative face.

`relativeTruncationConePartition` uses the coroot basis of the actual reduced
relative root system. The full Arthur weights are its coordinate maps. A
Weyl-invariant positive definite form pairs a simple coroot with a vector
as a positive multiple of the simple root evaluated on that vector. The
off-diagonal Cartan inequalities therefore give the obtuse-basis hypothesis.
The correspondence between subsets of this basis and standard parabolic
indices transfers the existence and uniqueness in the basis partition to
the stated coordinate regions.
