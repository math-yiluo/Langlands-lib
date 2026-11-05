# Restriction and the actual Picard square comparison

This internal construction compares the two ways of pulling an actual line
bundle around a commuting cube of schemes in a common universe. The bottom
square is `i₁ ≫ j₁ = i₂ ≫ j₂`, the top square is `ι₁ ≫ s₁ = ι₂ ≫ s₂`,
and the four face equalities are
`s₁ ≫ t = g₁ ≫ j₁`, `s₂ ≫ t = g₂ ≫ j₂`,
`ι₁ ≫ g₁ = g₀ ≫ i₁`, and `ι₂ ≫ g₂ = g₀ ≫ i₂`.

`comparisonIso` is a natural isomorphism from pullback along `t` followed
by the top square comparison to the bottom square comparison followed
by `SquareGluingRestriction.pullback`. Its components on the two legs
are the ordinary square pullback comparisons on the corresponding
faces. Thus it retains the specified ordinary comparison on the overlap,
and naturality applies to every actual bundle isomorphism.

The helper `cube_coherence` proves the compatibility of those components
with the overlap. It forgets through the core and line-bundle full
subcategory, identifies each ordinary Picard comparison with the ordinary
module comparison, and invokes
`Langlands.Scheme.Modules.SquareLocalIsoLift.cube_coherence`.
The component of `comparisonIso` is then `Comma.isoMk`; cancelling the
second face comparison reduces its compatibility equation to that helper.
Its naturality is the naturality of the two face comparisons.

`toOpenIso` specializes the natural isomorphism to the actual inverse-image
square of any open `U` of the total scheme. It uses the exact
`leftRestriction`, `rightRestriction`, and `SquareGluingRestriction.toOpen`
and their inclusion equations.

No cartesian, affine, field, nilpotence, properness, or finiteness
hypothesis is required. This is coherence infrastructure for the
infinitesimal gluing proof. It proves neither global object effectivity
nor full faithfulness of any comparison. Its provenance is internal:
the construction promotes the module cube coherence to actual Picard
arrows and uses the defining comma-category compatibility equation.
