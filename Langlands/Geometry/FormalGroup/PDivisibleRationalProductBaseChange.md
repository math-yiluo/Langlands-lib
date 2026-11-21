# Pullback of rational product maps

`baseChangeRationalProdIso` views the canonical comparison between the
pullback of a product of two p-divisible groups and the product of their
pullbacks in the category up to isogeny. Both groups and all integral maps
are the actual towers of finite group schemes.

`baseChangeRationalProdIso_naturality` identifies the pullback of a rational
block diagonal map with the block diagonal map of its two pulled-back
components through these comparisons. The proof composes with both product
projections and uses their pullback equations for the integral comparison.
On each factor, pullback takes the rational projection equation to the
needed equation because it preserves composition and integral maps.

This identity is derived from the Library's integral product comparison
and rational Hom. It supplies the product part of pullback for the split
rigidifier used by Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321),
before (6.17).
