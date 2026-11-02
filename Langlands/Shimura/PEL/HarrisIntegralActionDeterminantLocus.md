# Normalized determinant actions over a fixed abelian family

This is internal infrastructure for the division CM construction. It applies
the existing universal integral-action scheme, Cartier pullback comparison,
and global normalized determinant locus. No additional geometric existence
assertion from the literature is used.

Fix the actual Harris arithmetic data and normalized CM signature charts,
a locally noetherian scheme `S` over `Spec F`, and an actual abelian scheme
`B/S`. Supply a scheme `R/S` representing the underlying actual relative
endomorphism presheaf on the full locally noetherian test category, with the
stated natural comparison. Assume `R/S` separated and locally of finite type.

First, without these assumptions on `S` or `R`, the normalized determinant of
canonical relative restriction of any integral Harris-order action is
equivalent to the existing determinant pullback condition on that action.
The proof uses the actual equivariant rational isomorphism between direct
relative restriction and ordinary successive pullback, then the published
determinant predicate on rational-action classes. The equality of structural
maps in `Over S` identifies the maps to `Spec F`. The existing Lie base-change
naturality theorem therefore proves that canonical relative restriction
preserves the full normalized determinant. This defines a subfunctor of
actual integral actions on all schemes over `S`, using the existing canonical
restriction maps.

Under the hypotheses on `S` and `R`, `harrisIntegralActionDeterminantLocus`
is the existing global determinant locus applied to the rational extension
of the actual universal action on the raw-action locus. It is an actual
scheme over `S`. Its map to the raw-action locus is a closed immersion;
its structural map is separated and locally of finite type. Hence its
underlying scheme is locally noetherian.

For every locally noetherian test over `S`, a map to the raw-action locus
lifts precisely when its classified integral action on the original direct
pullback `B_T` satisfies the published all-family, all-chart normalized
determinant. This criterion follows from the global determinant
factorization theorem and the actual pullback comparison above.
The hom equivalence classifies every integral action satisfying this
condition. Its injectivity uses the monomorphism of the closed inclusion
and injectivity of raw-action classification; surjectivity uses the
factorization criterion. Its value is literally canonical restriction of
the universal raw action.

`harrisIntegralActionDeterminantLocusIso` gives the resulting natural
isomorphism from restricted `uliftYoneda` of actual scheme morphisms to the
determinant-action subfunctor, on the full locally noetherian test category.
Naturality follows by rewriting classification as restriction of the
universal action and applying the composition law for canonical relative-Hom
restriction.
The comparison retains the same original representatives, the positive
auxiliary Harris order, and the existing conjugated reflex structure in
the determinant condition. It allows disconnected or nonreduced tests.

This result remains conditional on the supplied relative-End representative
and its stated geometry. It does not construct the ordinary polarized
ambient moduli scheme, impose Rosati or level conditions, identify
rational-isogeny equivalence for the complete CM problem, or prove
smoothness, projectivity, or componentwise admissibility of that eventual
CM representative.
