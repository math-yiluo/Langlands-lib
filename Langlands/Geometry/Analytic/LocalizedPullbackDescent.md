# Pullback universal properties from refined strong maps

Author: Worker 250.

This internal categorical construction gives a sufficient condition for a
square of strong maps to become a pullback in the existing localized
analytic category. It does not construct analytic fibre products.

The coefficient field is complete and ultrametric. Its universe `u`, the
space universe `v`, and the atlas-index universe `w` are independent. No
Hausdorff or compactness hypothesis occurs.

`localizationFunctor_map_injective` derives faithfulness on complete strong
maps from the published source-quotient comparison and the finite-domain
bounded-algebra separation theorem. It concerns all stored bounded
pullbacks, including algebraic information invisible on ordinary points.

`exists_commonStrongNumerators` represents two localized arrows with the
same original source on one full quasi-isomorphism denominator. The actual
Ore construction applied to their denominators supplies the common source;
its numerator maps and square are complete strong maps. Denominator
cancellation gives the two exact equations in the localization.

`exists_commutingStrongNumerators` applies this construction to a commuting
localized cone over strong maps. Functoriality and the two numerator
equations give equality of the mapped strong composites. Faithfulness
reflects this equality, so the resulting strong cone commutes exactly.

`IsRefinedStrongPullback p q f g` is a Prop-valued definition requiring:

- The square of strong maps commutes.
- Every exactly commuting strong cone has a strong lift after a full
  quasi-isomorphism source refinement, with exact strong equations for
  both projections.
- Two strong arrows with the same two projected composites are equal as
  complete strong arrows.

`IsRefinedStrongPullback.exists_lift` first puts a localized cone on a
commuting strong source. Its supplied lift can require a second source
refinement. Composing the two full quasi-isomorphism denominators and
using the lift as numerator gives an actual right fraction. Cancelling
its denominator proves both localized projection equations.

`IsRefinedStrongPullback.hom_ext` puts two arbitrary localized arrows on a
common denominator. Faithfulness turns equality of each projected
localized composite into equality of the corresponding strong composites.
Strong joint uniqueness identifies the numerators. The common denominator
becomes an isomorphism in the localization, so it cancels.

`IsRefinedStrongPullback.isLimit` packages these existence and uniqueness
proofs into Mathlib's actual `IsLimit` for the mapped pullback cone.
`IsRefinedStrongPullback.isPullback` gives its `IsPullback` form. The test
objects and arrows in these conclusions range over the full original
localization. There is no assumption of faithfulness for the underlying
space functor, and no universe enlargement.

The provenance is an internal deduction from the published strong-source
separation, Ore construction and full right-fraction calculus. No external
literature result is transcribed. Constructing suitable squares and proving
étale base change remain separate geometric obligations.
