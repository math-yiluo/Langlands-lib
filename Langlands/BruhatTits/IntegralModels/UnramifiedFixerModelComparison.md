# Recovered models of apartment subsets and nearby root bounds

This internal supporting unit works at arbitrary universe `u` over a
nonarchimedean local field `F`, its actual inertia fixed field `K`, a smooth
affine group `G`, and supplied upper KP apartment data `D` for a torus
obtained by base change from `F`. It constructs comparisons between supplied
recovered fixer models and supplies the root bound needed by the nearby
parabolic-model reduction.

`normOneFixer_le_of_subset` uses literal inclusion of apartment subsets:
if `Ω₁ ⊆ Ω₀`, the character-valuation kernel intersected with the full
pointwise fixer of `Ω₀` is contained in the analogous group for `Ω₁`.
Every point fixed in the larger subset is fixed in the smaller one.
`comparisonOfRecoveredFixerModels` assumes actual lower and upper relative
component models, their compatible unramified recoveries, and those exact
full integral-image equalities. Under
`IntegralModel.UnramifiedSmoothHomExtensionStatement`, the recovered-model
comparison criterion turns the inclusion into an actual compatible full
and neutral model morphism, over the identity generic group. The definition
chooses this morphism. In particular, `Ω₀ = {x, y}` and `Ω₁ = {x}` give a
comparison from the two-point model to the model of `x`.

For the root bounds, the base change of the upper torus is maximal split in
connected reductive `G_K`. Supply upper opposite factor pairs, a split
torus `S` over `F`, and a factorization `S → T → G` of its map into `G`.
For an occurring lower root `a` and an actual point `g` of that root group,
`nonnegative_restrictedDepth_of_extend_mem_reducedFixer` assumes only that
the scalar extension of `g` fixes the given upper apartment point. Scalar
extension preserves root membership. The actual coarser-root intersection
with that full point fixer is the canonical restricted depth-zero subgroup,
by `restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero`. Reflecting
this membership through
`rootFiltration_torusFieldRestrictedRootFunctionFamily` gives nonnegative
torus-then-field restricted depth in the original lower field.

`nonnegative_restrictedDepth_of_full_integralPoints_le_fixer` combines this
with exact full recovery and a one-sided inclusion of the upper full
integral image in the point fixer. It does not need the upper full image to
equal that point fixer or its norm-one subgroup.
`nonnegative_restrictedDepth_of_integralPoints_fix_set` applies it at each
point of any apartment subset fixed by that image, using neutral-to-full
integral inclusion. Thus a model for `{x, y}` bounds depth at `y`.
These root bounds require no centralizer datum, V6 compatibility, lower
valuation, lower apartment, Galois fixedness or lower-torus maximality.

`parabolicRootComparisonsNear_of_recoveredFixerModels` assumes nearby
actual source models, their upper recoveries, actual comparisons to the
target with parabolic special-fibre image and exact parabolic reduction
preimage, and the one-sided upper full-image bound at the translated point.
It supplies every lower integral-root comparison in
`ParabolicRootComparisonsNearDescentTranslations`. Consequently the existing
radical-to-strict-positivity theorem applies when these geometric inputs
are supplied.

The provenance is internal composition of exact model recovery, the
generic-identity comparison criterion, the full restricted-root fixer
comparison, the exact scalar-filtration preimage theorem, and the nearby
parabolic root-comparison interface. No constancy of full point fixers on
facet closures is asserted. Existence of the actual recovered models,
unconditional Hom extension, parabolic special-fibre images and exact
preimages remain separate inputs. This unit does not prove the
unconditional depth-zero opposite-factor target.
