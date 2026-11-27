# Comparing a solution on an open where the entire law is defined

`BirationalGroupLaw.Solution.exists_iso_over_open` concerns an open of a
separated, reduced, Noetherian base. The law and the two open translation maps
are assumed to cover the entire relative square above that open. The restricted
domain inclusion and translations are therefore isomorphisms, by base change
of open immersions and the given pointwise coverage. Transport across the
product comparison for pullback makes the multiplication total and the
universal translations invertible on the restricted scheme.

Both maps of the common solution chart remain fibre-dense open immersions after
the restriction. `mul_eq_over` expresses the supplied `Solution.mul_eq` in the
category of schemes over the base. The proof sends a restricted test morphism to
the original base by composing with the pullback projection. The product
comparison and counit identities carry its coordinates to those of the original
law. Thus the supplied chart compatibility gives the compatibility of the
restricted products. `InvertibleTranslations.exists_iso_of_chart` now returns
an isomorphism from the entire restriction of `X` to the corresponding
restriction of the solution group, agreeing with the embedding of the
restricted chart.

For the generic open of a DVR, this provides the isomorphism used in the last
assertion of Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1
Theorem 5, printed p. 114 (PDF p. 121). The comparison is based on §5.1
Proposition 3 and Lemma 4, printed pp. 113–114 (PDF pp. 120–121). The literature
ID is `bosch-lutkebohmert-raynaud-1990-neron-models`, and the retained file SHA-256
is `16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
