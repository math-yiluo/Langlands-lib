# The exact integral-action image as an unpointed CM subpresheaf

This internal construction restricts the existing normalized CM tower presheaf
on `AdmissibleCMBaseCategory`, the full category of connected locally Noetherian
admissible actual schemes over the CM field. Its elements remain the original
compatible families at all actual algebraically closed geometric points.
The original Harris level category and all its transporter arrows are retained.
The actual integral order, positive auxiliary left involution, opposite
right-action convention, normalized determinant and geometric dimension, and
conjugated reflex scalar map are those of the imported constructions. All named
tensor, Picard, dual naturality, polarization, Weil, adelic and torsion inputs
remain explicit; the category supplies its existing geometric prerequisites.

`IntegralCMFamilyCondition` requires every evaluation of a compatible family
to lie in the exact image of normalized representatives with a supplied integral
order action on the same abelian scheme. `integralCMFamilyCondition_iff_at`
proves that this can be checked at any one actual geometric point. Its forward
direction evaluates the universal condition. Its reverse direction transports
the integral representative along the actual fibre-functor path used by the
canonical original comparison, then uses the given family's compatibility.
Thus no extra action or isogeny is descended from an arbitrary target object.

`IntegralCMUnpointedClassImage` is the corresponding subtype of the existing
unpointed value. Original level transport preserves the condition pointwise,
using the proved integral image stability for every original transporter.
`integralCMUnpointedClassImageTower` inherits its identity and composition laws
from the original family tower by subtype extensionality, and its inclusion is
a natural transformation on the entire original level category.

`integralCMFamilyCondition_pullback` proves preservation under each morphism
of the full admissible base category. At a target geometric point, the original
family pullback is the aligned actual pointed pullback of its source value at
the composed point. The imported aligned integral-image theorem preserves its
membership, using precisely the constrained dual family selected by the original
unpointed construction. The structure triangle is the actual `Over` morphism's
commuting equation. The same representative, normalization and supplied action
are transported; no integral-model existence assumption is introduced.

`integralCMUnpointedClassImagePullback` restricts that actual family pullback.
Subtype extensionality transfers its level naturality and the original
presheaf's identity and composition laws. The resulting
`integralCMUnpointedClassImagePresheaf` is an actual presheaf of level towers on
the full connected admissible test category. Its inclusion into the existing
normalized presheaf is natural both in base morphisms and in level transporters.

The provenance is this internal restriction of the imported actual normalized
family presheaf, using the proved point and base-change stability of its exact
integral-action image. The condition quantifies over existence of representatives
at the points; it does not choose a single simultaneous integral family.
There is no essential-surjectivity statement onto all rational CM classes,
no integral-model existence theorem, no componentwise disconnected extension,
and no representing scheme, smoothness, projectivity or output admissibility
conclusion. The host division representability proposition remains open.
