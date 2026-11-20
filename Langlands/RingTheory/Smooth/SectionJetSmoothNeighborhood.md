# Smooth neighborhoods from isomorphisms on section jets

Let \(R\) be noetherian and let an augmented map from a smooth
\(R\)-algebra \(P\) to a finitely presented augmented \(R\)-algebra \(A\)
induce surjections on all section jets. If an \(R\)-algebra \(B\) kills the
coefficient ideal of their kernels, the scalar extension of \(A\) to \(B\)
has a smooth principal open containing the entire section. The defining
element has augmentation one.

The proof works first over the quotient of \(R\) by the coefficient ideal.
That quotient is noetherian, and there the coefficient criterion gives
isomorphisms on all the actual jets. The induced map from the extended
\(P\) is étale at every section prime, so the extended \(A\) is smooth at
those primes. The closed complement of the smooth locus has an ideal
whose image under the augmentation is the unit ideal. A lift of one in
that ideal defines the smooth principal open. Tensoring that localization
with an arbitrary test algebra over the quotient preserves smoothness,
and the tensor comparison identifies the resulting principal open and
its augmentation.

This is an affine coordinate step in the construction of the smoothness
locus along a section in Raynaud, SGA 3, Exposé XV, Lemma 5.4, Gille–Polo
recomposition, pp. 267–268. The implementation uses a supplied smooth
source for the full jets and the local criterion by adic completion.
