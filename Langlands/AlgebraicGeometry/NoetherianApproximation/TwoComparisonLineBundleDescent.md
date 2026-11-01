# Finite algebra models of line bundles with two trivial restrictions

This internal development constructs finite algebra models of actual
line bundles together with triviality along two specified maps over the base.
It composes the published actual line-bundle descent theorem with the
simultaneous-isomorphism descent helper. It does not prove the valuation-ring
extension statement or the existence of normal finite ring stages.

`TwoComparisonDescent.overMap` is the base change of a morphism over a base
scheme. `transition` maps between base changes along a compatible map of base
schemes. Their projection equations follow from `pullback.lift`.
`transition_isPullback` cancels the defining right pullback square with
`IsPullback.of_right`. The theorem `overMap_transition` states the naturality
of these maps and follows by their two projection equations.
`comparison` maps a given base-change square to an intermediate stage, with
both projection equations. If the original square is a pullback, so is the
intermediate comparison square, again by cancellation.

The structure `TwoComparisonLineBundleModel` records an actual finitely
generated subalgebra `T` of an algebra `A` over `C`, an actual line bundle on
the base change of `X₀` to `Spec T`, and actual sheaf isomorphisms to the
structure sheaf along the base changes of two maps `Y₀ → X₀` over `Spec C`.
It also records a comparison recovering the given line bundle on `X`, along
every morphism to the stage compatible with both projections.

The existence theorem assumes that both `X₀ → Spec C` and `Y₀ → Spec C`
are quasi-compact and quasi-separated. The schemes `X` and `Y` fit into
given pullback squares over `Spec A`. Two maps `Y → X` respect both the
maps to `Spec A` and the given maps to `X₀` and `Y₀`. The given actual
line bundle on `X` has trivial restrictions along these two maps.
Every finite subset of `A` is contained in a stage carrying the bundle,
both trivial restrictions and the comparison just described.

First descend the line bundle to a finitely generated `C`-subalgebra `B`.
Construct comparisons from `X` and `Y` to the canonical base changes over
`B`, and use pullback composition and the given restriction isomorphisms
to compare the two pulled-back rank-one modules with the structure sheaf.
The simultaneous-isomorphism theorem gives a finitely generated
`B`-subalgebra `U` of `A` where both comparisons hold. Transitivity of
finite type makes `U`, with scalars restricted to `C`, a finitely generated
`C`-subalgebra. Pull back the original model from `B` to this final stage.
Naturality of the two maps and pullback composition give its two trivial
restrictions. The universal comparison from the first descent theorem
recovers the original bundle along every compatible comparison.

All rings and schemes lie in an arbitrary common universe `u`. No field,
valuation, normality or noetherian assumption occurs. The content is derived
from Library descent theorems and Mathlib universal properties; it is not a
new translation of a literature statement.
