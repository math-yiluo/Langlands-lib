# Generic extension from actual affine projectivity

This internal construction concerns an arbitrary valuation domain `R`,
the supplied fraction field `K`, and a smooth, geometrically connected,
universally closed, separated morphism `p : X ⟶ Spec R`.
Projectivity of the actual affine section algebras meeting the closed
fibre remains an explicit input.

`AffineClosedFibreSectionProjectivity p` is the proposition that for every
affine open `U` meeting the closed fibre, the actual section algebra
`Γ(X,U)` is projective over `R`, using exactly
`affineSectionAlgebra p hU` as its coefficient algebra.
It imposes no condition on affine opens missing the closed fibre.

`affineClosedFibreSectionProjectivity_of_integralFibreProjectivity` proves
that the published `IntegralFibreProjectivityStatement`, if supplied as
a hypothesis, implies this proposition. Smoothness supplies finite
presentation and flatness of the actual section algebra; geometric
connectedness, smoothness, and the closed-fibre intersection supply
geometric integrality of its actual spectrum map. The function then
applies the supplied proposition to those exact algebras. This is an
adapter to an explicit hypothesis, not a proof of the integral-fibre
projectivity statement.

`exists_lineBundle_of_closedFibre_frames_of_projective` takes an actual
cartesian generic square with maps `q : Y ⟶ X` and
`s : Y ⟶ Spec K`, a line bundle `D` on `Y`, and
`ClosedFibreGenericFrames q D p`. It also assumes
`AffineClosedFibreSectionProjectivity p` and injectivity of the actual
map `q.app U` for every total open. It concludes the existence of an
actual line bundle `E` on `X` with an actual module-sheaf isomorphism
between its pullback along `q` and `D.obj`.

The implemented proof uses the following geometry. The closed fibre is
integral, so its generic point supplies a reference index for the given
frame cover. Separatedness over the affine base makes all pairwise
and triple affine intersections affine. All the frame neighbourhoods
contain the chosen total image of the generic point of the closed fibre.
Thus their pairwise and triple intersections meet the closed fibre.
Universal closedness makes the given neighbourhoods cover all of `X`.

The proof applies `affineGenericScalarNormalization` on each reference
intersection, using the supplied projectivity predicate there. It then
applies `exists_lineBundle_of_normalized_frames`, using projectivity on
every pairwise overlap. Its total lifts and gluing construction provide
the actual bundle and restriction isomorphism. No further projectivity
or nonemptiness premise is introduced.

`lineBundleOfClosedFibreFrames` chooses the actual bundle provided by
this proof. `closedFibreFramesIso` chooses its actual module-sheaf
isomorphism under the original `q`.

`projectiveGenericLineBundleExtension` specializes the construction to
the canonical pullback of `p` along `Spec K ⟶ Spec R`.
It constructs the required frames with
`smoothClosedFibreGenericFrames` and supplies sectionwise injectivity
using `genericPullback_app_injective`.
`projectiveGenericLineBundleExtensionIso` gives an actual isomorphism
from the canonical generic restriction of this total bundle to the
original `D.obj`.

The provenance is internal: this module assembles the imported geometric
frame cover, affine intersection criterion, actual section-algebra
bridges, normalization, total-unit lifting, and gluing results.
It asserts no unconditional projectivity theorem or unconditional
two-axis extension theorem. All universes, valuation ranks, and supplied
fraction fields remain unrestricted.
