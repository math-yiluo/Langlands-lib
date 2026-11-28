# Vertices and density values for the weighted c-family round trips

Let `χ` be the cocharacter of the original standard Levi conjugated by the
normalizer point `n`, so that its Levi is `s·M` in Waldspurger's notation.
`weightedCAuxiliaryVertex` turns the two signed auxiliary cocharacters of the
c-map into gallery vertices with common Levi `levi χ`. The proof that they
share this Levi is `centralizer_auxiliary` followed by
`weightedC_conjugatedCocharacter_eq`. With the outer cocharacter `ζ'` of
`M'` these vertices are the parabolics `P_s = (M' ∩ s·P)U'` and
`P̃_s = (M' ∩ s·P)Ū'` of Waldspurger V.1, printed pp. 288–289.

`weightedC_regular_mul_ne_zero` states that a product of nonzero regular
functions on the unramified characters of the translated parameter scheme is
nonzero; these functions form a domain.
`rationalUnramifiedRegularFunctionsMap_iso_ne_zero` states that pullback
along an isomorphism of group schemes keeps a regular function nonzero.

`weightedCAmbientDensityValue` and `weightedCLowerDensityValue` give names to
the values of the ambient and lower Plancherel densities at a point of the
weighted domain `cWeightedDomain`. Their product with the inverse is the
weight `µ^G(ω) µ^{M'}(sω)⁻¹` of Corollary V.2.3, printed p. 294. The density
`µ = j⁻¹ ∏ γ(M_α|M)²` is defined at the start of V.2, printed p. 292
(source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
