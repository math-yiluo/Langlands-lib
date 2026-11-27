# Cuspidal trace class and discrete decomposition

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalSpectralStatement`
takes a connected reductive affine locally finite type group \(G\) over
a number field \(F\), and the parabolic-dynamic statement that
constructs the canonical proper radical family. It takes a central map
\(i:T\to G\) from a torus with a specified finite split presentation.
Pullback along \(i\) on rational characters is injective with finite-index
image. Haar measure on the common kernel \(G(\mathbb A_F)^1\) of the
rational character norms is assumed to be right invariant.

The positive real coordinates of the split torus are embedded diagonally
at infinity and give the image \(A_i\) in the full adelic group.
The measure on \(Q=A_iG(F)\backslash G(\mathbb A_F)\) is the pushforward of
the Library's Haar quotient measure on \(G(F)\backslash G(\mathbb A_F)^1\)
under inclusion. The statement asserts that the full almost-everywhere
cuspidal subspace \(S\) is closed in \(L^2(Q)\). For every proper rational
parabolic, its mass-one period over the actual unipotent quotient
converges and vanishes almost everywhere for Haar measure on the norm-one
group.

For each compactly supported continuous weight \(f\) with a Haar
integrability witness and the `IsAdelicTestFunction` condition, the
Bochner-integrated original right action against \(f\) is trace class on
\(S\). This test condition requires smooth archimedean slices and open
levels for both left and right finite translations. The integral uses
left Haar measure on \(G(\mathbb A_F)\).

There is a set of nonzero closed invariant subspaces of \(S\). Each has
only the zero subspace and itself as closed invariant subspaces. Their
inclusions form a Hilbert sum of \(S\), and each member is isometrically
equivalent, by an intertwiner for the adelic action, to finitely many
members. This is the finite-multiplicity conclusion for the cuspidal
space and its original right action.

The source is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Theorem 9.1.2 and Corollary 9.1.3, printed p. 241 (PDF p. 253),
and Lemma 9.3.1, Corollary 9.3.2 and Lemma 9.3.3, printed pp. 247–248
(PDF pp. 259–260). The source integrates smooth tests on
\(A_G\backslash G(\mathbb A_F)\). This derived statement uses full-group
weights on the same kind of positive rational quotient. For a split
component \(i\), the Library identifies \(A_i\) with \(A_G\) and the
transported measure uses the inclusion in (2.22), §2.6, printed pp. 68–69
(PDF pp. 85–86). The split-centre action on \(S\) is trivial in this
setting. The Hilbert-sum conclusion agrees with
`GroupSchemeFullAEL2CuspidalDecompositionStatement`, whose premise is
compactness of the integrated right action for every continuous
compactly supported weight. To obtain this premise, approximate a
continuous weight in \(L^1\) by its left convolutions with localized
smooth test kernels. The integrated operator of each approximation
factors through the compact smooth-test operator. The integrated-action
norm bound gives convergence in operator norm, and compact operators
are closed in that norm.
