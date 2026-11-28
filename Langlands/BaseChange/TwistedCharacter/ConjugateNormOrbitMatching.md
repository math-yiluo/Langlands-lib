# Adjoints on the frequency orbits of conjugate compact types

Let \(A\) be a proper finite-dimensional ultrametric normed algebra over
a proper nontrivially normed ultrametric field of characteristic zero.
Use a second-countable topology, a compact open exhaustion and the Borel
structures on \(A\) and its units. Embed \(A^\times\) openly by \(i\) in a
topological group \(H\). Suppose an algebra automorphism \(\gamma\) preserves
the self-dual bicharacter and induces ambient conjugation by \(y\in H\)
on units. The algebra map on the compact subgroup intersection is then
\(\gamma^{-1}\), whose adjoint on frequencies is \(\gamma\).

`conjugateNormOrbitMatching` applies to two smooth finite-dimensional
compact types on small norm subgroup images with the prescribed
exponential orbit character sums. If their interaction on the conjugate
intersection has a nonzero intertwiner, there is a frequency in the
second orbit whose image under \(\gamma\) lies in the first orbit. Both
orbits include translations by the respective dual lattices. The proof
restricts the ambient intertwiner to the norm-unit intersection and
applies `normOrbitIntertwining`. The image of the first exponential
ball under \(\gamma^{-1}\) lies in the necessary convergence saturation.

For Hausdorff \(H\), `conjugateNormFixedOrbit` specializes this result
using the trivial representation on the second level. A nonzero fixed
vector gives an intertwiner from the trivial type. The compact character
pairing is symmetric up to inversion of its integration variable, so a
nonzero intertwiner also exists in the reverse direction. The trivial
representation has the singleton frequency zero in the character sum.
Its orbit modulo the dual lattice is that dual lattice, giving a
frequency in the first orbit from the adjoint image of the second
level's dual lattice. These are the self-intertwining and fixed-vector
applications of the frequency matching in Clozel's Lemma 9.
[Clozel 1987, §§3.6–3.7, printed pp. 158–164](https://doi.org/10.4153/CJM-1987-008-3)
