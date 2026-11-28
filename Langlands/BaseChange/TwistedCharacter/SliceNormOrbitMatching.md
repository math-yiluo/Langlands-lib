# Projecting ambient compact frequencies to an interacting slice

Use proper finite-dimensional ultrametric normed algebras \(A,B\) over a
proper nontrivially normed ultrametric field of characteristic zero, with
the stated countability, compact open exhaustion and Borel structures.
Let \(j:A\to B\) be an algebra map, and let \(p:B\to A\) be a continuous
additive map adjoint to it for the given self-dual bicharacters. Embed the
units of \(B\) openly into a topological ambient space that is a group.

`sliceNormOrbitMatching` compares the two small norm congruence types,
once the ambient type is transported through the open subgroup image chart.
Suppose both smooth finite-dimensional types have the given exponential
orbit character formulas and the ambient type intertwines nontrivially
with the slice type on the slice intersection. Then there is an ambient
frequency in its orbit modulo the ambient dual lattice whose projection
belongs to the slice orbit modulo the slice dual lattice.

Continuity of \(j\) gives a small radius whose ball maps into the ambient
exponential convergence ball. Pull the supplied intertwiner back to the
norm-unit intersection, then use compact Haar inversion to reverse the
direction of the nonzero intertwiner. Applying `normOrbitIntertwining`
with the specified adjoint gives the claimed projection. For the fixed
algebra of a semisimple adjoint, the projection for the trace pairings is
provided by `fixedTraceProjection`. This is the slice application of
Clozel's Lemma 9. [Clozel 1987, §3.6, printed p. 158](https://doi.org/10.4153/CJM-1987-008-3)
