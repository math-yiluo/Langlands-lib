# Polynomial growth independent of a closed matrix embedding

This derived construction uses the published
`RepresentationGrowth.closedImmersionHeightDomination` for the Library's
unchanged mixed-space matrix-and-inverse height. It applies to arbitrary
number fields and actual group schemes. The two finite matrix ranks can be
zero; affineness, connectedness and reductivity are not additional premises.

`HasPolynomialGrowth.of_closedImmersion` transfers a polynomial bound for
any matrix representation `sigma` to the height of a representation `rho`
that is a scheme-theoretic closed immersion. If
`height sigma ≤ D * (height rho)^e` and
`‖f‖ ≤ C * (height sigma)^d`, the resulting bound has constant `C * D^d`
and exponent `e*d`. Both are chosen before the point quantifier.
`hasPolynomialGrowth_iff_of_closedImmersions` applies this in both
directions when both representations are closed immersions.

The existing polynomial-growth submodules are therefore equal inside the
original ambient complex function module.
`polynomialGrowthChangeRepresentation` is the corresponding complex
linear equivalence, which is the identity on underlying functions. Its
action compatibility keeps the original formula `R(g)f(x)=f(x*g)`.
The equivalence and its inverse have identity underlying maps, so their
linear and inverse laws follow directly.

`uniformPolynomialBound_of_closedImmersion` and its two-embedding
equivalence treat an arbitrary indexed family of functions. They preserve
the quantifier pattern `∃ d, ∀ j, ∃ C ≥ 0, ∀ g, ...`: one common exponent
and constants that may depend on the index. The height-domination degree
is fixed before all indices, so the new common exponent is again `e*d`.
The family index can lie in an independent universe and can be empty.

No differential operators are constructed or identified by these family
lemmas. They prove neither smoothness nor existence of a closed embedding,
and they do not replace the Library height by an adelic product norm from
the literature. Their provenance is the internal height-domination theorem
and elementary nonnegative power inequalities.
