# Induced progenerator independence from the maximal-Levi block theorem

`InducedProgeneratorIndependenceFromMaximalLeviBlockStatement` says that
`MaximalLeviBlockStatements` implies `InducedProgeneratorIndependenceStatement`
over the same field and carrier universes. The premise is the maximal-Levi block
corollary of Renard VII.1.3. The conclusion compares the normalized inductions of
a norm-kernel summand induction for arbitrary rational parabolics with conjugate
Levi embeddings, as in VI.10.1.

## Opposite maximal parabolics

`inducedProgeneratorMaximalOpposite_of_maximalLeviBlockStatements` compares
opposite parabolics \(P\) and \(Q\) with the same embedded rational Levi \(M\).
Write \(A\) for the norm-kernel summand induction of the irreducible
\(\rho_0\) supplied with the supercuspidal \(\pi\). Equal parabolic ranges give
the comparison `leviInductionIsoOfRangeEq`. If a normalizer outside the Levi
fixes inertia, the proof transfers its twist intertwiner from the universe lift
back to \(\pi\) and applies `inducedProgeneratorIso_of_inertialNormalizer`.

In the remaining case, \(Q\) is proper because a Levi of the full group has full
range, which would force \(P\) to have full range as well. Maximality of \(P\)
gives a character on the common split component whose kernel of pairing with
cocharacters annihilates every relative root. If this character pairs nontrivially
with some cocharacter, cross multiplication expresses the pairings of every
relative root in terms of its pairing at that cocharacter. If the character pairs
to zero everywhere, every relative root does too. Both cases give proportional
relative-root pairings for the common Levi, so
`isMaximalParabolic_of_proportional_splitComponent_pairings` gives maximality
of \(Q\).

An inertia relation between the lifted \(\pi\) and a normalizer pullback would
give a twist intertwiner for the inverse normalizer by evaluating it at
\(\phi^{-1}m\). Thus both ordered pairs of opposite parabolics satisfy the
disjoint-inertia hypothesis of `mixedJacquetInertialProjection`. This gives
split projections \(r_P i_Q A \to A\) and \(r_Q i_P A \to A\), each inducing a
bijection on maps into objects of the Levi inertia block. The proof uses the
coinvariant quotient equivalence to transport supercuspidality to the universe
lift of \(\pi\) and `inertiaRelated_iff_twistIntertwiner` to express membership
in the Levi block of VII.1.3.

## Comparison by first adjointness

For an irreducible subquotient \(\tau\) of \(i_P A\), VII.1.3 gives a twist
\(\sigma\) of the lifted \(\pi\) such that \(\tau\) is a subquotient of the
irreducible \(i_P \sigma\). Compose the projection \(r_P i_Q A \to A\) with
a nonzero map \(A \to \sigma\). The section makes the composite nonzero, and
first adjointness gives a nonzero map \(i_Q A \to i_P \sigma\). Its target is
irreducible, so the map is surjective. Subquotient transitivity puts \(\tau\) in
the occurrence block for \(Q\). Essential surjectivity in VII.1.3 now gives an
object \(X\) of the Levi block with \(i_Q X \simeq i_P A\).

Transpose \(r_Q i_P A \to A\) by first adjointness to obtain
\(f : i_P A \to i_Q A\). For each Levi block object \(Z\), full faithfulness of
\(i_Q\) identifies maps \(i_Q A \to i_Q Z\) with maps \(A \to Z\).
Under first adjointness, precomposition by \(f\) corresponds to precomposition
by the mixed Jacquet projection, hence is bijective. Surjectivity for \(Z=X\)
gives a map \(g : i_Q A \to i_P A\) with \(g \circ f = 1\). Injectivity for
\(Z=A\) then gives \(f \circ g = 1\). This yields the opposite maximal isomorphism.

`inducedProgeneratorIndependence_of_maximalLeviBlockStatements` applies
`inducedProgeneratorIndependence_of_maximalOpposite` to carry this comparison
along the common-Levi gallery, with conjugation transporting to the original
Levi embeddings.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.10.1, Lemma, Proposition and Corollary (printed p. 207,
PDF p. 213), and VII.1.3, Corollary (printed p. 226, PDF p. 232). The comparison
uses the split mixed Jacquet filtration from VI.5.3(iii) and the irreducibility
and equivalence clauses of VII.1.3.
