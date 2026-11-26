# Proof of the transporter-coset comparison in Renard VII.1.3

`Langlands.GroupScheme.standardLeviTransporterCosets` proves
`Langlands.GroupScheme.StandardLeviTransporterCosetsStatement.{u}`.
The comparison uses the left coset sets of V.4.4 for every standard Levi
index \(I\). The proof extends the split-torus conjugacy argument of
V.4.3.3 to a possibly different target Levi.
[Statement](StandardLeviTransporterCosetsStatement.md) · [V.4.3.3 proof](StandardLeviNormalizerQuotientProof.md)

Suppose \(gL_I(k)g^{-1}=L_J(k)\). The conjugate of the chosen split
torus has its points in \(L_J(k)\) since \(T(k)\subseteq L_I(k)\).
The density criterion `SubgroupFunctor.range_le_of_localField_points`
gives containment of its range in the represented standard Levi
\(L_J\) on all scheme-valued points. The original torus factors through
\(L_J\) because \(L_J\) contains the centralizer of \(T\). Both factorizations
are maximal split tori because their composites into \(G\) are maximal.
`standardLeviSplitComponentStatement` gives connected reductivity of
\(L_J\), so `maximalSplitTorusConjugacy` supplies a point \(m\in L_J(k)\)
conjugating the first factor to the second up to an isomorphism of the
tori. Functoriality of the inner automorphisms gives \(n=mg\in N_G(T)(k)\).
Conjugation by \(m\) preserves \(L_J(k)\), so \(n\) has the same
Levi target as \(g\). Since \(n^{-1}g=g^{-1}m^{-1}g\in L_I(k)\),
the left cosets \(nL_I(k)\) and \(gL_I(k)\) agree.

Two normalizer points \(n,m\) represent the same Weyl coset precisely
when the Weyl image of \(n^{-1}m\) lies in \(W_I\). The published
`StandardMaximalLeviWeyl.mk_mem_iff_mem_levi` identifies this with
\(n^{-1}m\in L_I(k)\), precisely equality of their point cosets.
The proof chooses a normalizer representative of each Weyl coset and
maps it to its point coset. The equivalence of the coset relations gives
both independence of the choice and injectivity. The construction of
\(n\) from \(g\) gives surjectivity. `Equiv.ofBijective` packages the map,
and the equality of point cosets for any two representatives of the
same Weyl coset gives the representative rule in the statement.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026. VII.1.3, first paragraph, printed p. 224
(PDF p. 230), and V.4.3.3 and V.4.4, printed p. 119 (PDF p. 125).
Registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
