# From affine line-bundle extension to arbitrary targets

This is a derived local-to-global construction from the published affine and
general extension propositions, actual line-bundle pullback, strict atlas
realization and geometric atlas enlargement. It introduces no external
literature assertion. Every scheme and the chart index retain arbitrary
universe `u`.

The conclusion `of_affine` is the unchanged
`OpenImmersionLineBundleExtensionStatement.{u}`, conditional on an explicit
proof of `AffineOpenImmersionLineBundleExtensionStatement.{u}`. This
contribution proves the reduction and does not prove the affine hypothesis.

`exists_compatible_chart` assumes the affine extension proposition, an open
immersion `v : V ⟶ X` into a locally Noetherian scheme, factorial stalks
outside its range, an actual line bundle `L` on `V`, and any point `x` of
`X`. It produces an open `T` containing `x` and an actual module-sheaf
isomorphism between the pullback of `L` and the pullback of the trivial
bundle on the ambient fiber product `V ×[X] T`.

The proof chooses an affine open neighborhood `W` of `x`. The base change
`V ×[X] W ⟶ W` is an open immersion. Its complement is the inverse image
of the complement of `v`; the stalk-ring isomorphism for `W ⟶ X`
transports factoriality to this complement. Applying the affine hypothesis
extends the restriction of `L` to an actual line bundle `E` on `W`.
A trivializing neighborhood `U` of the point of `W` above `x` maps openly
to `X`. Its open image `T` is isomorphic to `U`. Pulling the local
trivialization across this isomorphism gives an actual trivialization of
the pullback of `E` to `T`. The canonical map from `V ×[X] T` to
`V ×[X] W`, together with pullback composition and square comparisons,
then gives the required overlap isomorphism. The point `x` need not lie
outside `V`.

`chartFamily j D` is the fixed small family indexed by `Option X.Opens`.
The `none` chart is the original source `Y`, its map is `j`, and its bundle
is the given `D`. A `some U` chart is the open subscheme `U`, its map is
the inclusion, and its bundle is trivial. This family does not enumerate
arbitrary line bundles or their isomorphism classes.

`singletonRealization F i₀` realizes the singleton chart selection using
the chart's own source scheme, open immersion, module, identity map and
identity-pullback comparison. Equality transport identifies each index of
the singleton with `i₀`. `exists_good_atlas` takes the graph of its induced
actual transitions; the common module witnesses every triple, so the
published strict-atlas graph lemma gives a good atlas.

`maximal_region_eq_top` considers a maximal good atlas distinguished by
`none`. Its actual realization is a line bundle on the covered open
region. Since `none` belongs to the atlas, the original range of `j` lies
in this region. Consequently factoriality outside `j` implies
factoriality outside the region. For every point `x`, the compatible-chart
lemma applied to the realized bundle gives a trivial chart `some T` near
`x` with the required actual overlap identification. The geometric
`maximal_contains_chart` lemma places this chart in the atlas. Its image
is contained in the region and contains `x`. Thus the region equals the
top open, with no compactness or separation assumption.

`of_affine` starts from a singleton good atlas and applies the strict
maximal-extension theorem. The coverage result makes the region's
inclusion into `X` a scheme isomorphism. Pullback of the actual glued line
bundle along its inverse produces the extension on `X`. The composition,
identity and inverse-isomorphism pullback comparisons identify its
pullback to the region with the glued module. Pulling this identification
back along the distinguished chart and composing with that chart's
realization comparison gives exactly the actual module-sheaf isomorphism
required by the original general extension proposition.

All local Noetherian and factoriality assumptions are those of the two
published propositions. The construction adds no integrality,
connectedness, separatedness, quasi-compactness, projectivity or bundle
hypothesis. It uses none of the prohibited valuation-ring or relative-dual
extension conclusions. Publication of this reduction alone does not prove
the general extension theorem; a proof of the affine hypothesis remains
necessary.
