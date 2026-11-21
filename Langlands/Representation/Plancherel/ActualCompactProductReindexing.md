# Polynomiality of the actual translated compact coefficient map

Waldspurger’s V.3 formula (1) uses left translation on both induced factors
before the standard tensor. IV.1 uses fixed compact carriers and one regular
denominator for an entire operator. The original is registered as
`waldspurger-2003-plancherel`, printed pp. 276–277 and 295, PDF pp. 42–43 and 61.

`translationFactorization_of_conjugateCompact` proves the published compact
translation factorization for `K' = gKg⁻¹`. It reads the actual compact tensor
through the fixed product-section equivalence. The restriction equivalence
untwists its values, and the pointwise translation evaluates the original
section at `(g, g)⁻¹ * x`. The conjugate inducing equivalence has the identity
vector map. After removing the twists, the value transport is the fixed
conjugation of the vector and its smooth dual, with each underlying functional
preserved.

After the right action by `(g, g)`, evaluation at `k ∈ K' × K'` therefore reads
the original compact section at `(g, g)⁻¹ * k * (g, g) ∈ K × K`. This is
independent of the parameter and agrees with the same composition at the unit
character. Taking the right action by `(g⁻¹, g⁻¹)` yields the factorization.
The proof uses injectivity of the fixed product-section evaluation and the
published full product action on the compact tensor.

`compactTranslation_polynomial` uses that factorization and the published
polynomiality of the actual right action. For supplied numerator and
denominator data of the actual pulled-back standard tensor,
`compactChartContinuation_of_conjugateCompact` transports the numerator into
the exact V.3 chart and retains its denominator on the simultaneous generic
locus. In `ActualTranslatedCompactChart`, the rationality corollary also uses
the explicit reverse-dual scalar input. The closed V.3.1 extension, unitarity and preservation statements are separate
published targets.
