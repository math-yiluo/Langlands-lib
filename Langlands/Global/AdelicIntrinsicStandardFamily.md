# The intrinsic standard family in a standard Levi

For a standard index \(Q\), `intrinsicStandardFamily` uses the same maximal
split torus and generic cocharacter inside the actual Levi \(M_Q\).
`intrinsicStandardRootData` obtains the lower simple roots \(Q\) and the
preimage descriptions of the lower standard parabolics, Levis and radicals.
To apply `standardLeviStandardFamilies`, the proof identifies the ambient
torus factor in \(M_Q\) with the torus in the given family by cancellation
against the closed Levi inclusion.

For \(I\subseteq Q\), `intrinsicNestedLeviIso` identifies the Levi indexed by
\(I\) in the intrinsic family with the ambient \(M_I\). The standard Levi
nesting theorem places \(M_I\) inside \(M_Q\). The preimage formula and
uniqueness of representatives give the isomorphism and its equality after
composition with the inclusions into the ambient group.

`IntrinsicStandardCompactStatement` gives the compatibility needed in the
rank induction of Lemma 7.2. It assumes that \(K\) is compact with
\(P_0(\mathbb A)K=G(\mathbb A)\), that its inverse image in every ambient
standard Levi is maximal compact, and that \(K\cap P_0(\mathbb A)\)
centralizes the specified positive torus. The inverse image \(K_M\) in
\(M_Q(\mathbb A)\) then has intrinsic minimal Iwasawa coverage, and
\(K_M\cap P_{0,M_Q}(\mathbb A)\) centralizes the positive torus in the
Levi. The proof uses the intrinsic minimal height constructions for
these properties. For every standard Levi of \(M_Q\), the preceding
isomorphism takes its compact inverse image to the corresponding ambient
Levi's compact inverse image, so maximality follows along the induced
topological group isomorphism. If \(Q\) is proper, it has strictly smaller
cardinality than the ambient finite set of simple roots.

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal p. 23, (7.3), p. 28,
(7.23)–(7.24), and the application of Theorem 7.1 to \(M_Q\) in the
proof of Lemma 7.2 on p. 29.
