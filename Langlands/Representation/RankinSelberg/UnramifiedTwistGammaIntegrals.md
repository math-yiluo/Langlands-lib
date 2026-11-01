# Unramified gamma coefficient and integral transport

This module supplies internal algebraic helpers for transporting a supplied gamma certificate. It does not assert existence of gamma factors. Two determinant characters χ₁ and χ₂ are each trivial on −1 and have product |·|ᵘ. Choosing either character to be trivial will cover both positions of an unramified twist on the original representation carriers.

`character_weyl` uses the existing determinant recurrence, and `character_blockWeyl` identifies the determinant of the actual block Weyl element. `character_neg_one` derives the required sign condition from the absolute-value formula. The functional `functional` keeps the original linear map, `coefficient` identifies the actual common-vector coefficients, and `minusOne` preserves the same model scalar for every coefficient-image vector by surjectivity of `modelMap`.

The forward products acquire |det|ᵘ. In the actual dual functions, inverse transpose replaces the determinant by its inverse. The Weyl determinants contribute one, so both equal-rank and right-translated complementary-block dual products acquire |det|⁻ᵘ. This uses the actual transformation definitions, without identifying them with contragredient models.

`equal_integral_shift` and `unequal_integral_shift` descend the pointwise product identities to the total integrals. They use the published integrand shift identities, and require no extra convergence hypothesis. `equal_forward` and `unequal_forward` shift the parameter by +u, retaining every test function and every rectangular decomposition. `equal_dual` and `unequal_dual` shift by −u, retaining the same Fourier partner and the actual complementary rectangular measure and right Weyl translation.

These are internally derived transport identities for the published JPSS definitions. The conventions are Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions* (1983), registered as `jpss-1983-rankin-selberg`, equations (2.4), printed p.387, and (2.7)(iii), pp.390–391. No analytic existence, irreducibility, Whittaker-type, or multiplicativity result is used.
