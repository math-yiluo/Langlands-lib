# Calibrating isolated norm-one trace identities at a finite place

`NormOneFinitePlaceCalibratedTraceStatement` uses the norm-one subgroups of
two affine group schemes locally of finite type over a number field. A common
central split torus satisfies the character restriction hypotheses for each
norm-one decomposition. The chosen norm-one Haar measures are right invariant.
Each automorphism fixes the respective torus morphism, and each selected
rational norm-one point has a commutative twisted centralizer.

At the distinguished finite place, each side uses a Borel group, an ambient
Haar measure and one compatible pair of centralizer and quotient measures.
The centralizer measures are right invariant, finite on compact sets and
positive on open sets. On each side, two local tests multiply the same exterior
function, which is invariant under right insertion of the distinguished
finite-place group. The resulting adelic tensors are averaged over the
normalized positive torus.

Suppose the traces for both pairs equal the respective weighted geometric
terms for every compatible norm-one geometric measure package. Suppose also
that the same nonzero scalar relates the two traces for each pair. If the
ordinary trace for the first pair is nonzero and its two local orbital
values agree, the two local orbital values for the second pair agree.

`normOneFinitePlaceCalibratedTrace` uses `normOneFinitePlaceGeometricTerm`
to choose one geometric measure package on each side and to factor the two
orbital integrals. On the ordinary side the nonzero first trace forces a
finite rational covolume and nonzero local and exterior orbital values.
`calibratedTraceExtraction` then cancels the common local value from the
first trace identity and uses the resulting ratio of geometric weights
in the second identity.

This is a derived step for the distinguished-place extraction in
Henniart–Lemaire (2011), I.6.8, pp. 49–50, which isolates a single rational
orbit on each side. Here a pair with equal local orbital values determines
the weight ratio for the isolated trace identities.
