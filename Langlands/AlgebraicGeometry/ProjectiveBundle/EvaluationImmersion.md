# Closed immersion of projective evaluation

Let `p : X → S` be an actual morphism of schemes in an arbitrary common
universe, `M` an actual module sheaf on `S`, `L` a line bundle on `X`,
and `ev : M → p_* L` an actual module-sheaf morphism. Assume that `M` is
locally free of rank `n + 1` and that the evaluated basis sections on
every chosen frame open generate pointwise. The existing construction
then gives `evaluationMap : X → frameBundle M n hM`.

For every frame open `U`, `isPullback_evaluationMap_chart` proves that
the square with top map

`localEvaluationMap : (p⁻¹U).toScheme → RelativeProjectiveSpace U.toScheme n`

and bottom map `evaluationMap` is Cartesian. Its vertical maps are the
actual inclusion of `p⁻¹U` into `X` and the actual projective frame chart.
This conclusion concerns the full inverse image of the chart.

The proof uses two existing Cartesian squares. The outer square is the
inverse-image-open square for `p`; the structure-map equations identify
its horizontal maps with the composites of the evaluation maps and the
two projective structure maps. The right square is the projective frame
chart square over `U → S`. The actual evaluation chart equation supplies
commutativity of the left square. Cancellation of the right Cartesian
square proves that the left square is Cartesian.

`evaluationChartPullbackIso` is the resulting canonical scheme isomorphism
from the actual open `p⁻¹U` to the categorical pullback of global evaluation
along the projective frame chart. Its two projection equations give the
actual open inclusion and the actual local evaluation map.

`evaluationMap_property_iff` consequently detects every morphism property
that is Zariski local at the target on these actual local evaluation maps.
The forward direction restricts along the Cartesian chart square.
For the converse, the projective frame charts cover the target. Their
categorical pullback maps are isomorphic to the actual local evaluation
maps by the proved square. Invariance under isomorphisms and descent on
that open cover give the global property.

`isClosedImmersion_evaluationMap_iff` specializes this result to closed
immersions. `isClosedImmersion_evaluationMap_of_evaluationGenerates`
uses the intrinsic `EvaluationGenerates` condition to supply the frame
generation premise, and retains closed immersion of the actual local
evaluation maps as its explicit geometric input.

This is an internal derived consequence of actual projective frame
gluing, evaluation, Cartesian-square cancellation, and Mathlib's
target-local morphism-property API. It introduces no external literature
assertion. It does not prove generation or local closed immersion for
the cubic bundle of an abelian scheme, the cubic direct-image rank, or
ordinary polarized full-level moduli representability.
