# Proof of the unipotent scheme product for a rational Bruhat cell

`Langlands.GroupScheme.rationalBruhatFactorization` proves
[`RationalBruhatFactorizationStatement`](BruhatFactorizationStatement.md):
for a connected reductive group \(G\) over a field \(k\), a maximal
\(k\)-split torus \(i : T \to G\), a generic cocharacter \(\nu\) of \(T\)
with \(\chi = i\circ\nu\), and a rational point \(n\) of the torus
normalizer, put \(\psi = n\chi n^{-1}\). Then multiplication
\[
(U(\chi)\cap U(\psi^{-1}))\times_k(U(\chi)\cap U(\psi)) \longrightarrow U(\chi)
\]
of the scheme-theoretic intersections is an isomorphism. The proof works
with test-scheme points throughout and concludes by Yoneda.

## Reduction to two cocharacters of one torus

The automorphism of \(T\) induced by \(n\) (`normalizingAut`) transports
\(\nu\) to a cocharacter \(\xi\) of \(T\) with \(i\circ\xi = \psi\)
(`groupHom_cocharacterAut_comp`). Since \(\nu\) is generic, the published
`genericCentralizer` gives \(Z_G(\chi) = Z_G(T)\), and
`centralizer_conjugate_eq_torusCentralizer` gives \(Z_G(\psi) = Z_G(T)\) as
well. Hence \(Z_G(\psi)\le Z_G(\chi)\) as subgroup functors. The remaining
argument (the private lemma `isIso_of_common_commutativeGroup`) uses only
that \(G\) is smooth and affine over \(k\), that \(\chi\) and \(\psi\) factor
through one commutative group scheme, and this centralizer containment.

## The opposite cell and its stability

By the published opposite-cell theorem `oppositeCellStatement`, the
multiplication \(m : U(\psi^{-1})\times P(\psi)\to G\) of the affine
representatives is an open immersion. Because \(\chi\) and \(\psi\) factor
through one commutative group scheme, the image of \(\chi\) normalizes the
subgroup functors \(U(\psi^{-1})\) and \(P(\psi)\)
(`unipotent_isNormalizedBy_range_of_common_commutativeGroup`,
`parabolic_isNormalizedBy_range_of_common_commutativeGroup`), so the open
\(m\) is stable under conjugation by \(\chi\) (`isCocharacterStable_product`).
Multiplication \(U(\psi^{-1})\times P(\psi)\to G\) is injective on the points
of every test scheme (`hasInjectiveOppositeCellMultiplication_of_isAffine`).
The two scheme-theoretic intersections represent the subgroup functors
\(U(\chi)\cap U(\psi^{-1})\) and \(U(\chi)\cap U(\psi)\)
(`isRepresentedBy_subgroupIntersectionHom`).

## Lifting an orbit extension into a stable open

The private lemma `Dynamic.IsOrbitExtension.exists_lift_of_cocharacterStable`
states, for a separated group scheme \(G\) over any base and any test
scheme \(X\): if \(e\) is the
\(\chi\)-orbit extension of a point \(g\) over \(X\times\mathbb{A}^1\), \(j\)
is a \(\chi\)-stable open immersion into \(G\), and the zero value of \(e\)
factors through \(j\), then \(e\) itself factors through \(j\).

Its proof first treats a field-valued point \(b : \operatorname{Spec}K\to X\)
(the private lemma `fieldOrbit_range_subset`). The restriction of \(e\) along
\(b\) is again an orbit extension. Its composite with the polynomial
presentation of the affine line over \(K\) is a morphism
\(\operatorname{Spec}K[t]\to G\), and the inverse image of the open is a
scalar-invariant open of \(\operatorname{Spec}K[t]\): for an extension field
\(L\), a scalar \(a\in L^\times\) and \(t\in L\), the value at \(at\) is the
\(\chi(a)\)-conjugate of the value at \(t\) (`IsOrbitExtension.eval_scale`),
an \(L\)-point lies in the open exactly when it factors through \(j\), and
factoring through \(j\) is preserved by \(\chi\)-conjugation
(`IsCocharacterStable.factors_iff`). The inverse image contains the zero
point, so `AffineLine.range_subset_of_isScalarInvariantOpen` puts the whole
image in the open; the polynomial presentation is an isomorphism
(`AffineLine.polynomialPointInv`), so the image of the restricted extension
lies in the open too. For a general test scheme, each point of
\(X\times\mathbb{A}^1\) is the image of the closed point of its residue
field, through a field-valued point of \(X\) and a point of the affine line
over that field. So the image of \(e\) lies in the open, and
`FiniteEtaleImage.liftOver` lifts \(e\) through the open immersion. The
lift is a morphism of schemes over the base, so nonreduced test schemes are
included.

## Bijectivity on test-scheme points

Let \(X\) be a test scheme.

*Surjectivity.* Let \(g\) be an \(X\)-point of \(U(\chi)\). It has a
\(\chi\)-orbit extension \(e\) whose zero value is \(1\), and \(1 = m(1,1)\)
lies in the opposite cell. The lifting lemma factors \(e\) through \(m\),
so `hasProductContraction_of_represented_lift` writes the contraction of
\(g\) as a product of extensions with factors in \(U(\psi^{-1})\) and
\(P(\psi)\). By normalization and injectivity,
`HasProductContraction.exists_unipotent_factors` gives \(g = xy\) with
\(x\in U(\psi^{-1})\), \(y\in P(\psi)\) and \(x, y\in U(\chi)\). The
normalized-limit criterion `mem_unipotent_of_mem_unipotent_of_mem_parabolic`,
applied with \(Z_G(\psi)\le Z_G(\chi)\), puts \(y\) in \(U(\psi)\). The points
\(x\) and \(y\) lift to the two intersections, and their pair maps to \(g\)
because the inclusion of \(U(\chi)\) is a monomorphism.

*Injectivity.* If two pairs have the same product in \(U(\chi)\), their
images in \(U(\psi^{-1})\times P(\psi)\) have the same product in \(G\), so
they agree by opposite-cell injectivity. The inclusions of the
intersections are monomorphisms, so the pairs agree.

Multiplication is thus bijective on the points of every test scheme, and
`isIso_of_yoneda_map_bijective` makes it an isomorphism.

## Sources

The decomposition is Borel–Tits, *Groupes réductifs* (1965), §5.13(1),
p. 99, in the order used in the proof of §5.15, p. 100, and the variety
product in Milne, *Algebraic Groups* (2017), §25.27, p. 551. The Lean proof
follows a different route: the dynamic opposite open cell over all test
schemes, as described above.
