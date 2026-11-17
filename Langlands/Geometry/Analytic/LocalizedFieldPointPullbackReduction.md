# Strong-map reduction for full field-point pullback preservation

This internal categorical reduction retains independent universes for the
complete ultrametric coefficient field `K`, the analytic spaces and their
chart indices, and the complete algebraically closed ultrametric value field
`L`. It uses the actual localization, its existing étale predicate, and its
full field-point functor.

`StrongEtaleFieldPointPullbackStatement K L` asks the full field-point functor
to preserve every localized pullback whose four arrows are images of
complete strong morphisms and whose left leg satisfies `strongEtale`.
The pullback premise is the actual localized categorical universal property;
it is not a pointwise square or a pullback in a replacement category.

`localizedEtaleFieldPointPullbackStatement_of_strong` proves that this
restricted preservation assertion implies the original preservation
assertion for all localized arrows. First choose original presentations for
the four localized objects and full right fractions for the cospan arrows.
Compose each projection with the inverse denominator of its cospan arrow.
The common-strong-numerator theorem places these two composites on one full
quasi-isomorphism source. This produces a square of mapped strong arrows
isomorphic to the original square. Composition of étale arrows and the
mapped-arrow comparison show that its strong left numerator is étale.
Transfer the categorical pullback along the four isomorphisms, apply the
restricted preservation assertion, then transfer its image back along the
field-point functor's images of those same isomorphisms. Every edge equation
is an equality of complete localized arrows.

`strongEtaleFieldPointPullbackStatement_iff` records the exact equivalence.
Its reverse direction specializes the original assertion to mapped strong
arrows and uses the same strong/localized étale comparison.

The provenance is internal: the proof combines the existing full
right-fraction calculus, common strong numerators, the actual étale
composition and comparison results, and categorical invariance of pullback
squares under isomorphisms. This unit does not establish the remaining
geometric preservation assertion for strong squares and does not prove the
host task's unconditional target.
