# Unit-axis restrictions of the actual Mumford additivity equation

This internal categorical helper defines the two unit axes of the parameter
product and verifies the restrictions of the actual Mumford parameter-additivity
equation to both axes. It does not prove the equality on the whole product.
The relative geometric cube criterion remains a separate obligation.

The first axis is `x ↦ (x,e)`, and the second is `y ↦ (e,y)`, with the actual
unit points and the chosen cartesian monoidal product in `Over S`.
The group unit laws show that the composite of either axis with multiplication
is the identity. `mumfordBundleClass` is the existing compatible-isomorphism
class of the actual normalized parameter-first `mumfordBundle`, with its
specified inverse and evaluation, and with its existing rigidification.

`mumfordBundleClass_one` applies the published `mumfordZeroParameterIso` on
an arbitrary test scheme. Thus it concerns the actual full zero-parameter
family, with its rigidification, rather than just its geometric points.

For either axis, successive parameter pullbacks agree with pullback by the
composite, by the published compatible composition isomorphism; identity
pullback is compatible with the identity by the published identity isomorphism.
Pullback of the tensor is the tensor of the pullbacks, by the canonical tensor
comparison and its proved compatibility laws. The two projections of the axis
are the identity and the unit point, in the appropriate order. The unit-point
pullback of the Mumford class is trivial; removing it by the corresponding
rigidified tensor unitor proves the stated axis equality.

All geometric inputs of these comparisons are precisely the abelian scheme,
the line bundle rigidified along the unit, the supplied ordinary inverse and
evaluation, and invertibility of the canonical pullback-tensor comparisons.
The base scheme is arbitrary, and there is no reducedness, field, dual-scheme,
Picard-zero or representability assumption. The proof uses published categorical
coherence theorems internally. The implemented comparisons follow directly
from the published constructions; this module introduces no additional claim
from original literature and supplies no geometric cube theorem.

`Langlands.AbelianScheme.classesPullback_comp` is public for reuse by the
closed-agreement reduction. It identifies two successive pullbacks of rigidified
classes with pullback along the composite, using `relativePullbackComp` on a
representative. Its original statement and proof are unchanged.
