# Comparison of neutral centralizers and neutral fixer models

Fix maximal-unramified building data `C` for the actual generic group.
Let `D₁` and `D₂` be supplied smooth affine full models with their relative
identity components. Assume that the full integral-point subgroup of `Dᵢ`
is the character-valuation kernel intersected with the pointwise fixer of
the apartment image of `Ωᵢ`. All constructions use the original generic
identifications at arbitrary universe `u`.

The theorem `unramifiedNeutralCentralizerModel_integralPoints_eq` identifies
the integral-point subgroups of the actual centralizers constructed inside
the two neutral models when both apartment subsets are nonempty. These
subgroups lie in the rational points of the same prescribed centralizer
`C.centralizer.Z`. Neither boundedness nor any torus-Iwahori or simply
connected normalizer statement is assumed.

The comparison proceeds in one direction with only `Ω₁.Nonempty`.
An integral point of the first neutral centralizer maps into the first
neutral model, and hence the first full model. Its ambient image lies in
the character-valuation kernel and fixes one apartment point. The
centralizer translation formula and apartment-map injectivity imply that
the translation vector in the apartment's translation space is zero.
It therefore fixes every apartment point, so its ambient image is integral
in the second full model. This proves
`map_unramifiedNeutralCentralizerModel_integralPoints_le_full`.

The first neutral centralizer is smooth with geometrically connected
fibres. The strict-Henselian smooth homomorphism extension theorem extends
its prescribed generic inclusion to the second full model. Geometric
connectedness factors that homomorphism through the second neutral
component. The exact integral-point preimage formula for the second
neutral centralizer gives
`unramifiedNeutralCentralizerModel_integralPoints_le`. Reversing the two
models gives the equality.

The theorem `unramifiedNeutral_integralPoints_eq_of_sharpFixer_eq` then
identifies the two neutral integral-point subgroups whenever their sharp
fixers agree and both apartment subsets are nonempty. It substitutes
the centralizer equality and the supplied sharp-fixer equality into
`unramifiedNeutralRootCentralizerGroup_eq_neutral` for each model.
The construction `unramifiedNeutralSharpFixerEquiv` packages this equality
as a multiplicative equivalence. Its ambient rational-point coercion
is unchanged, as stated by `coe_unramifiedNeutralSharpFixerEquiv`.

This is internal derived content from the actual centralizer construction,
centralizer translations, generic apartment injection, smooth extension,
connected factorization and neutral generation. Worker 200 suggested
comparing the centralizer contributions for nearby fixer sets. The result
assumes that both full models are already supplied; it does not construct
them, prove torus-Iwahori comparisons or complete the host parahoric-model
statement.
