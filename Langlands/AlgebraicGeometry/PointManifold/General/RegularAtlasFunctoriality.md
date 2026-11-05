# Actual maps for universe-general regular atlases

Let `k : Type u` have `RCLike k`, and let `X` and `Y` be affine objects
over `Spec k`. For any supplied regular atlases `A : RegularAtlas k X d`
and `B : RegularAtlas k Y e`,
`RegularAtlas.contMDiff_postcomp A B f` proves that the actual relative
point map `p ↦ p ≫ f`, for `f : X ⟶ Y`, is real `C∞` between the two
explicit charted spaces. The coefficient universe is arbitrary; the
source and target dimensions are arbitrary natural numbers. No analytic
assumption on `f`, manifold assumption, positive dimension, or existence
of points is required.

The identity family on the source is `RegularSmooth` because each global
regular evaluation is smooth by
`General.RegularAtlas.contMDiff_regularEvaluation`. Pulling back those
regular functions along `f`, using `General.RegularSmooth.postcomp`,
proves the same test property for the actual postcomposition map.
`General.RegularAtlas.contMDiff_iff_regularSmooth` for the target then
gives actual manifold smoothness. That published criterion accepts a
charted source without a source manifold hypothesis.

`RegularAtlas.postcompDiffeomorph A B f`, for an actual relative
isomorphism `f : X ≅ Y`, constructs a real `C∞` diffeomorphism. Its
forward and inverse functions are respectively `p ↦ p ≫ f.hom` and
`q ↦ q ≫ f.inv`. The inverse laws use categorical associativity and the
two inverse equations of `f`. Both smoothness fields are applications
of `contMDiff_postcomp`. `postcompDiffeomorph_maps` records the two
function values by definitional equality.

`RegularAtlas.independence A B` applies that construction to `Iso.refl X`
when both atlases live on the same actual point carrier. The resulting
underlying equivalence is exactly `Equiv.refl`, by `Category.comp_id`.
Its two charted-space structures remain explicit, including when they
have the same carrier and different model dimensions. Empty point
spaces and zero dimensions are included. This is independence up to the
specified identity diffeomorphism; it does not equate chosen atlases.

The carrier throughout is the published `PointTopology.RingPoint k X k`,
with its existing topology from global regular-function evaluation.
This module chooses no atlas and supplies no algebraic chart-existence
theorem.

This is an internal universe generalization of Worker 383's actual-map
helper constructions in
`PointManifold.RegularAtlasCanonicalityProof`, using the independently
published `General.RegularAtlasComparisonProof` and
`General.RegularEvaluation` APIs. Worker 94 adapted those constructions
and exposed the identity comparison directly. No original-literature
theorem is transcribed here.
