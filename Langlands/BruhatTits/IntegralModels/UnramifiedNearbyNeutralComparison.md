# Nearby neutral groups of recovered apartment fixer models

This internal adapter concerns the actual maximal unramified extension of a
nonarchimedean local field at arbitrary universe `u`. It retains the supplied
upper apartment data, connected reductivity of the original group, maximal
splitness of the upper apartment torus, the centralizer datum, and full integer
valuation compatibility. The models are supplied
`RecoveredApartmentFixerModels`: each includes the original lower model, an
upper model, compatible full and neutral unramified recovery, and the exact
upper full character-valuation one-fixer formula.

For two nonempty apartment subsets with equal sharp fixers,
`upper_neutral_integralPoints_eq_of_sharpFixer_eq` identifies the upper neutral
integral-point subgroups. It packages the original apartment as
`buildingDataOfApartment` and applies
`unramifiedNeutral_integralPoints_eq_of_sharpFixer_eq`. That theorem compares
the actual neutral centralizer contributions and combines their equality with
neutral root-centralizer generation.

The lower subgroups are the inverse images of the upper ones under the same
original rational scalar-extension homomorphism, by
`UnramifiedComponentModelRecovery.neutral_integralPoints_eq_comap`.
Rewriting these formulas gives
`lower_neutral_integralPoints_eq_of_sharpFixer_eq`.
`lowerNeutralSharpFixerEquiv` packages this equality as a multiplicative
equivalence preserving each ambient rational point, as its coercion lemma
records.

If `x` belongs to the closed facet of `y`, the two-point sharp fixer for
`{x, y}` equals the singleton sharp fixer for `{y}`. The AS4 hypothesis needed
for that comparison follows from the supplied integer-valued building data.
Consequently
`neutral_integralPoints_pair_eq_singleton_of_mem_facetClosure` gives both
upper and lower neutral integral-point equalities for any recovered models
of these two sets.

On each descended line through `x`, the original point lies in the closed
facet of the translated endpoint on a real neighbourhood of zero.
`eventually_recovered_neutral_integralPoints_pair_eq_singleton` applies the
preceding comparison to arbitrary supplied families of recovered pair and
endpoint singleton models. One neighbourhood gives both the upper and lower
equalities, and the parameter may have either sign.
`RecoveredFixedNearbyModels.eventually_source_neutral_integralPoints_eq_endpoint`
specializes this to the actual pair sources in the existing nearby-model
package.

These results compare integral-point subgroups; they do not assert equality
of full point fixers or of integral group schemes. They require the recovered
models as inputs. Their existence, parabolic special-fibre images, exact
reduction preimages, and the final opposite-factor assertion remain separate
obligations. The adapter is derived from the existing recovery, neutral
comparison, and nearby-facet results and asserts no new transcription from
original literature.
