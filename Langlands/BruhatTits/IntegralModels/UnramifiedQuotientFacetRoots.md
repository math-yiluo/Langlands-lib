# Quotient roots give ordinary roots vanishing on the facet

This internal supporting unit works at arbitrary universe `u` over a
nonarchimedean local field. It uses supplied parahoric building data `P`,
the apartment axioms and root-reflection property, an injective equivariant
comparison with a supplied maximal-unramified building, a zero datum upstairs,
and a relative-component model whose neutral integral points upstairs are the
zero subgroup intersected with the pointwise fixer of the translated apartment
subset. The subset is required only to be nonempty.

The supplied integral torus has generic inclusion `P.i` followed by the actual
inner automorphism associated to `g`. It is closed and split. The special-fibre
quotient is the actual maximal reductive quotient specified by
`Q.IsReductiveQuotient`. The proposition `IntegralOppositeFactorsStatement`
remains an explicit hypothesis throughout.

`mem_facetDerivativeRoots_of_quotient_root` proves that if the canonical
specialization of a generic character is an actual quotient root, the original
character belongs to `facetDerivativeRoots`. Thus it is the derivative of an
ordinary affine root, in the noncontainment sense of the existing
`P.affineRoots`, which vanishes identically on the subset. The original
character is preserved, including its root length.

The proof first uses actual quotient-root support and transport through the
inner isomorphism to show that the original character is a relative root of
`P.i`. Perfect-residue integral lifting supplies an integral generic-root
point whose quotient reduction lies outside the doubled root subgroup.
The residue field of a nonarchimedean local field meets the perfect-field
hypothesis of that lifting theorem.

Pulling the point back by the inner isomorphism gives a nonidentity original
root point. Its conjugated image is integral and outside the actual radical
preimage: membership in that preimage would force its quotient reduction to
be one, contradicting the doubled-subgroup exclusion. The assumed opposite
factor statement makes both actual opposite factors integral after
conjugation, and hence their reflection product is integral. The integral
reflection criterion then shows that the point's valuation functional
vanishes everywhere on the subset.

The point belongs to the whole depth group of its own valuation functional.
`facetOrdinaryRootOfQuotientExclusion` uses the same quotient exclusion to
certify that this precise functional is ordinary. Its derivative is the
original character, so this proves the asserted membership.

`facetDerivativeRootOfQuotientRoot` packages the inverse-specialized quotient
character as a member of the actual derivative-root set. Its character
formula is definitional.

This is a composition of the named Library and separately submitted internal
supporting results, with no new external-source formulation. It proves one
direction of the root-set comparison. It does not prove the opposite-factor
statement, the converse root-set inclusion, or the full derivative root datum.
