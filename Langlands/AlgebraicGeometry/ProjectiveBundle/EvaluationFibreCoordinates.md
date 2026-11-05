# Actual evaluation coordinates on residue-field fibres

This internal derived construction concerns the actual evaluation map into
the projective frame bundle of a locally free module of rank `n + 1`.
It retains the explicit hypothesis that its actual frame evaluation
sections generate. The base, source, and module are otherwise arbitrary
in a common universe.

First, a morphism to the source inverse-image frame open, together with
a compatible change of base into that frame open, pulls back the actual
local evaluation sections. The existing relative linear-system pullback
theorem shows that their relative map, followed by the changed frame
chart, is the original evaluation precomposed with the source map.
The proof uses the implemented local chart equation of the glued
evaluation morphism.

For a point of the original base lying in a frame open, the actual
source-fibre inclusion factors through the inverse-image open by the
open-immersion lifting property. Its projection agrees with the original
residue-point lift to the frame open, by the fibre square and cancellation
of the open immersion.

The sections `fibreEvaluationSections` are the genuine local evaluation
sections pulled back along that source lift. Pullback of generating
sections proves their generation. Their relative linear-system map
`fibreEvaluationCoordinates` is defined over the original residue field.
The general change-of-base equation identifies its composite with the
actual projective-fibre chart with the original evaluation on the source
fibre. Both pullback projection equations then identify the map into the
whole actual projective fibre with the canonical map of pullbacks induced
by evaluation.

The construction uses only actual open lifts, the existing fibre and
projective chart constructions, and relative linear-system pullback.
It does not identify the coefficient module with the full direct image
of the fibre line bundle, prove invertibility of direct-image base change,
or prove cubic rank, generation, very ampleness, or moduli representability.
