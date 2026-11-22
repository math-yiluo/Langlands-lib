# Reduction of adelic local finiteness to a compact boundary model

`UniformGrowthLocalFinitenessBoundaryModelStatement` asks for a weighted Hilbert
model at each base parameter of the published
`UniformGrowthLocalFinitenessStatement`. The model uses one reproducing equation
with nonvanishing eigenvalue at the base point. The Hilbert operator families
are weakly holomorphic, the left operator at the base point is a topological
embedding, and the right operator there is compact. Each test kernel in the
equation has a continuous linear smoothing realization into a common
uniform-growth Fréchet space.

The compatibility condition says that the right operator vanishes on the
kernel of the combined smoothing at the base point. For each solution at a
growth exponent at least the chosen exponent, the model supplies a lift into
the Hilbert kernel whose smoothed evaluations agree with the combined original
convolution. The coefficients in both combinations are normalized by the
reproducing eigenvalue. The model uses two independent Hilbert universes.

`uniformGrowthLocalFiniteness_of_boundaryModel` proves that the construction of
such models implies the published target. A closed-range left inverse reduces
the difference of the Hilbert operators to the exact-base-fibre Fredholm
criterion. At the base point the range of its finite-dimensional family is
exactly the Hilbert kernel. If smoothing kills a vector in that kernel,
compatibility makes the right operator zero there, and injectivity of the left
operator forces the vector to vanish. Continuous point evaluations separate the
growth space and extend injectivity to a neighbourhood. On that same
neighbourhood the witnessing family at each larger growth exponent is the
composition with the continuous injective growth comparison. Evaluation of an
actual solution's lift and its reproducing equation give the range containment.

This is a conditional reduction of the final argument in Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §7.6, pp. 219–220,
with the same boundary operator form for the central variant in §7.7. The
exact-base-fibre criterion makes compatibility at the base point sufficient
for the injectivity step.
