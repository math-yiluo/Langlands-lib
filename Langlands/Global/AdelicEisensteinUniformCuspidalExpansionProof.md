# The uniform cuspidal expansion of convergent Eisenstein series for finite families

`Langlands.Global.eisensteinUniformCuspidalExpansion` proves
`Langlands.Global.EisensteinUniformCuspidalExpansionStatement.{u}` at any universe `u`.
For a fixed finite family of inducing functions and a standard parabolic, the theorem
chooses a threshold, competing Weyl data for the identity element and a polynomial degree
bound before quantifying over the regular parameter and the coefficients. The resulting
expansion is tested against cusp forms by absolutely convergent pairings of its terms on
the norm-one Levi quotient. [Statement](AdelicEisensteinUniformCuspidalExpansionStatement.md)

## Proof

The proof takes `parabolicLeviCenterRestriction` at universe `u` and passes it to
`arithmeticHarishChandraFiniteness_of_leviCenterRestriction`. The latter obtains
arithmetic finiteness from rational adelic finiteness by extending functions from an
arithmetic quotient to their finite adelic double coset. Then
`parabolicHarishChandraFiniteness_of_arithmetic_and_center` uses arithmetic finiteness
and the finite center restriction to obtain finiteness on parabolic quotients from
restriction to the corresponding Levis.
[Center restriction](../Automorphic/GroupSchemeLeviCenterRestrictionProof.md),
[arithmetic finiteness](../Automorphic/GroupSchemeArithmeticHarishChandraInduction.md),
[parabolic finiteness](../Automorphic/GroupSchemeHarishChandraParabolicReduction.md)

`eisensteinUniformCuspidalExpansion_of_parabolicHarishChandraFiniteness` uses that
finiteness to obtain a finite-dimensional span of positive split-component translates.
This gives the generalized exponent decomposition used in the uniform scalar comparison.
The comparison uses the Library proofs of constant-term automorphy and Levi cusp-form
rapid decay. The identity Weyl specialization identifies the selected intertwining
integral with the twist of the inducing function. For the finite family, the reduction
chooses a threshold dominating all the single-function thresholds, concatenates the
competing labels and takes the supremum of the degree bounds. Linearity of the constant
terms and pairings then assembles the identity for each coefficient vector.
[Exponent decomposition](AdelicAutomorphicExponentDecompositionReduction.md),
[uniform expansion reduction](AdelicEisensteinUniformCuspidalExpansionReduction.md)

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), §6.10, pp. 208–209, derive the comparison of cuspidal
projections in Corollary 6.10 from the constant-term formula. Equation (6.21)
takes the identity Weyl element in (6.20), and the pairing in §6.2, (6.8), gives
the norm-one tests. The Lean proof obtains the scalar identity using the exponents
of the full constant-term components of the remaining full-target pieces. The
single-function degree bounds come from those fixed components and thus apply
uniformly over the parameter. [Bernstein–Lapid](https://doi.org/10.1090/jams/1020)
