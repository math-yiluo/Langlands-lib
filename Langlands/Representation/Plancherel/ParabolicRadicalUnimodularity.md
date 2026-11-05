# Unimodularity of a supplied geometric parabolic radical

This is an internal consequence of the published compatible-presentation
comparison and the published dynamic-radical unimodularity theorem. It does not
assert existence of geometric radicals or compatible presentations.

`parabolicRadical_isUnimodular` works over an arbitrary nonarchimedean local
field, with a connected reductive ambient group scheme and exactly the canonical
rational-point topology. Local compactness and the nonarchimedean group
structure remain explicit, as in the conditional intertwining target.

For a supplied geometric radical `n : U ⟶ P`, the proof uses
`ParabolicRootPresentation.range_comp_radical_eq` to identify its full ambient
image with the dynamic identity-limit group of the presentation's actual
split-component cocharacter. Ambient smoothness follows from connected
reductivity. The proof transports closedness across this equality and applies
`Aubert.General.DynamicNormalization.dynamicUnipotent_isUnimodular`, then
transports its conclusion back. It requires no inducing representation,
characteristic restriction, or additional geometric-radical existence result.
