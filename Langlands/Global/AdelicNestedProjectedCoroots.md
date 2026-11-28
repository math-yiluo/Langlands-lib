# Projected coroots at nested truncation levels

`NestedProjectedCorootsStatement` compares the truncation projections of two
connected reductive groups with a common maximal split torus. The torus
embeddings must factor through the specified group homomorphism. The same
generic cocharacter defines the simple systems, and the index set of the
projection is contained in both simple systems. The two linear projections on
the real cocharacter space agree. Projecting the coroot of a root shared by the
two groups therefore gives the same vector at either level.

The proof uses `sameTorus_realCoroot_eq` on each shared coroot to identify the
spans of the coroots in the index set. Both projections have image the common
root annihilator and kernel this coroot span. The proof decomposes a vector
using the intrinsic projection, then applies the ambient projection to the two
summands.

`levelProjection_nested` compares two nested levels in the same group. The
projection to the larger index set kills the coroot span of the smaller one.
`weight_levelProjection_outside` shows that an ambient fundamental weight for
a root outside the projection index set reads the same coordinate before and
after projection. This follows from the Kronecker pairing of the ambient
fundamental weights with the simple coroots.

In Delorme's decomposition (7.26), take the second group to be the standard
Levi \(M_Q\) and use the index of \(P_1 \subseteq Q\) for both projections. The
retained intrinsic coroots for \(P_1 \cap M_Q\) are then the ambient projected
coroots for the simple roots in the Levi of \(Q\) outside the Levi of \(P_1\).
The outside weights give the coordinates of the complementary split factor.

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §3.1 and §7, journal pp. 24–25 and 30,
especially (7.8) and (7.26).
