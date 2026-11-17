# Convergence and bilinearity of actual Schwartz conjugation pairings

This is an internal analytic component of the actual-point VIII.3.1 proof.
It is derived from the Library's translation stability and its weighted
square-integrability criterion for the Schwartz space. It does not prove
the weighted square estimate or the chamber decay conclusion.

For a group with an open-measurable topological structure and a compact open
subgroup, `Space.integrable_conjugationIntegrand` assumes `TranslationWeights`
and `L2Weights` for a measure and proves integrability of
`g ↦ f₁(h g h⁻¹) f₂(g)` for all Schwartz functions `f₁`, `f₂` and all `h`.
The translate `Space.translate ht h⁻¹ h⁻¹ f₁` evaluates to
`f₁(h g h⁻¹)`. Both this translate and `f₂` belong to `L²` by
`Space.memLp_two`, and Mathlib's `MemLp.integrable_mul` proves integrability
of their complex product. The integral is bilinear.

On actual rational points of an affine group scheme locally of finite type
over any nonarchimedean local field, fix a compact open Iwasawa subgroup `K`
for the chosen minimal standard parabolic and a nonempty finite matrix
representation `ρ`. The retained analytic hypothesis is exactly
`SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight ρ)`.
The theorem `integrable_rationalConjugationIntegrand` obtains the required
translation bounds from `rationalTranslationWeights` and the square bounds
from `rationalL2Weights`, and applies the generic result.
No closedness of `ρ` or Haar property of `muG` is required once this local
analytic hypothesis is supplied. No relation of `K` to the height subgroup
is required.

`rationalCuspidalConjugationConverges_of_squareIntegrableWeight` specializes
this to the published intrinsic cuspidal convergence conclusion. The proof
works for every Schwartz function in the first argument, so it ignores
the cuspidality premise. It does not identify the intrinsic kernel with
any recursive construction.

`rationalConjugationPairingBilinear` packages the actual pairing as a
complex bilinear map with values in all complex functions on the group.
The addition laws use the proved integrability and the Library's integral
addition lemmas; the scalar laws use its integral scalar identities.
Its application theorem identifies it pointwise with the existing
`rationalConjugationPairing`. No continuity or measurability of the resulting
function of the conjugator is asserted here.
