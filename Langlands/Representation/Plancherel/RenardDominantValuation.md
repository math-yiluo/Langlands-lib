# Normalization and chamber transport for Renard's centralizer valuation

Author: Worker 1292.

This internal derived helper uses the actual rational points, actual character
valuation, actual cocharacter uniformizer section, and actual restriction
evaluation map of the published `RenardDominantComparisonStatement`. It retains
universe `u`, every nonarchimedean local field in either characteristic, and an
arbitrary morphism `s : S → Z` with the displayed bijectivity proof `h`.
The helper does not need splitness or reductivity.

`uniformizerRealValuation` is the additive map obtained by composing the
actual uniformizer section, the rational-point map of `s`, and the real
centralizer valuation. Additivity follows from their homomorphism laws.

`centralizerValuation_uniformizerSection` proves that the real centralizer
valuation of `s(c(π))` is `1 ⊗ c`. It uses uniqueness of the character
normalization, functoriality of the integer valuation under restriction, and
the published intrinsic uniformizer evaluation formula
`CocharacterUniformizer.rationalCharacterValuation_latticeSection`. This
formula holds for actual characters and cocharacters without a coordinate
presentation. It also fixes the positive sign.

The uniformizer membership lemma evaluates every positive root on this pure
tensor. Casting the integer pairing to the reals preserves nonnegativity.
`C0Plus_eq_inter_dominant` then proves the exact equality `C0Plus = C0 ∩ D`
by unpacking the images of the uniformizer section in both directions.

Equality of integer character valuations implies equality of the real
centralizer valuations: apply injectivity of `restrictionEvaluation s`
and its character normalization. Consequently chamber membership is constant
on each integer valuation fiber.

`centralizerValuationImageEquiv_image_dominant` represents each point of the
actual real valuation range by an actual rational point and uses the published
pointwise formula for `centralizerValuationImageEquiv`. It identifies the two
actual chamber images, without replacing either range by an integral
cocharacter lattice.

`isDominantValuationSection_inter` cuts any full integer valuation section by
the chamber. Injectivity restricts from the full section; surjectivity follows
by choosing the full representative and using the fiber invariance just
proved. The last theorem transports a dominant section to a bijection under
the range-restricted real centralizer valuation, using the same canonical
image equivalence and the same invariance.

The provenance is an elementary comparison and restriction of the published
maps. The conventions and intended chamber cuts are those of Renard,
*Représentations des groupes réductifs p-adiques* (9 July 2026), registered
source `renard-2026-representations-groupes-reductifs-padiques`, V.2.3,
V.2.5, and V.3.21–V.3.23 (printed pp.105, 107, 116–117; PDF pp.111, 113,
122–123). The proof here is the implemented map comparison, rather than
an invocation of the source's structural assertions.

This helper proves the first three comparisons and the general section-cut
mechanism. It does not prove the existence of a full lattice transversal,
the positive finite cover, actual centralizer structure, finite index, or
the complete `RenardDominantComparisonStatement`.
