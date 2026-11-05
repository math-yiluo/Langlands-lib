# Valuative coefficient and root integrality targets

Author: Worker 1563.

This internal auxiliary unit supplies the elementary coefficient and root
comparison needed by the spectral approach to whole-group anisotropic
compactness. It derives its meaning from the existing Mathlib polynomial,
valuation, and matrix definitions. It is not an additional assumption of the
whole-group compactness target.

`Langlands.ValuativePolynomialRootsStatement.{u, v}` quantifies over fields
`F : Type u` and `E : Type v`, their given valuative relations, an algebra
structure, and `ValuativeExtension F E`. The latter requires that the algebra
map preserve and reflect the valuative comparison. For a monic polynomial
`p : Polynomial F` which splits over `E`, all coefficients of `p` satisfy
`coeff ≤ᵥ 1` if and only if every root of its mapped polynomial in `E`
satisfies `root ≤ᵥ 1`. Repeated roots are allowed. Every natural-number
coefficient is quantified, including those beyond the degree.

`Langlands.ValuativeMatrixRootsStatement.{u, v}` specializes the comparison to
the actual characteristic polynomial of an `F`-matrix on `Fin N`, with its
entrywise image in `E`. The splitting premise is explicit. The degree `N`
includes zero; in that case the characteristic polynomial is one and there
are no roots.

`Langlands.ValuativeSpectralIntegralityStatement.{u, v}` is the conjunction
of these two targets. Neither topology, local compactness, characteristic,
separability, nor nontriviality of the valuation is assumed. The two field
universes are independent.

The intended elementary proof lifts integral coefficients to the canonical
valuation ring. A root of a monic lifted polynomial is integral over that
ring, and valuation rings are integrally closed in the valued field.
Conversely, a split polynomial's coefficients are integral expressions in
its roots and its leading coefficient. Mathlib implements these facts in
`Valuation.Integers.isIntegral_iff_v_le_one` and
`Polynomial.isIntegral_coeff_of_factors`. Compatibility of the valued
extension transports coefficient comparisons, and `Matrix.charpoly_map`
gives the matrix specialization. These are provenance and proof-route
explanations; this file records proposition targets only.

This unit supplies no group-theoretic spectral boundedness criterion,
rational-point density, valuation extension, or anisotropic eigenvalue
argument. Those remain obligations of its consumers.
