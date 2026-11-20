# The equal-rank cuspidal residue period

`residuePairing` integrates the product of two realized cusp forms over the subset \(1 \leq |\det g| < e^n\) of \(GL_n(F)\backslash GL_n(\mathbb A_F)\), using the restriction of the Library's quotient Haar measure. `residuePairing_eq_residueConstant` identifies it with the exponent-zero constant in the equal-rank continuation by pulling the restricted quotient measure back to the rational fundamental domain intersected with the determinant slab.

The uniform Siegel-cover estimate `exists_band_cover_uniform` bounds the supremum along a compact part of each real Lie curve. Applying it to the determinant slab proves that these suprema are square integrable. The product of two cusp functions is therefore integrable, and the integral is linear in each vector.

When the product central character is trivial, a central scalar corrects any right translation to determinant norm one without changing the product being integrated. The corrected translation preserves the restricted Haar measure. This gives finite and compact invariance. For the real Lie action, differentiate the translation-invariant integral at zero. The derivative of the product is dominated by a sum of products of the square-integrable suprema for the original vectors and their Lie derivatives. This proves the Lie invariance required by `IsInvariantPairing`.

For irreducible cuspidal realizations, a nonzero value of this period with trivial product central character gives contragredience by the Library's invariant pairing criterion. The bilinear form is used with the second realization as its first argument, so `isContragredientOf_of_residueConstant_ne_zero` concludes that the first realization is the contragredient of the second.

Cogdell (2004), *Analytic Theory of L-functions for GLₙ*, §2.3, p. 210 (PDF p. 213, `cogdell-2004-analytic-theory-gln`), identifies the period in both residue terms as a Petersson pairing and relates it to duality. The determinant-slab realization and the proof of operator invariance implement the direction from a nonzero period to contragredience for the Library's cuspidal spaces.
