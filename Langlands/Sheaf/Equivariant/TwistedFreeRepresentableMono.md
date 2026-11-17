# Lifted representables with monomorphic structure maps

This internal consequence of the twisted-category definitions assumes a global
lift `L`, a local action system `S` consisting of lifts, and a monomorphism
`L.obj.hom` from the represented object to the base. The theorem
`GlobalLift.eventuallyEquivariant_of_mono` proves
`L.EventuallyEquivariant S`.

For each ordinary arrow into `L.obj`, the two intertwining composites have the
same inverse twist by the two lift conditions. Their composites with the
structure map therefore agree by the defining equations of twisted arrows.
Monomorphism cancellation identifies their underlying arrows, and twisted
extensionality identifies the arrows themselves. The fixing open subgroup is
the whole source subgroup; no further shrinking is required.

No continuity, compactness, analytic rigidity or lift-existence result is used.
With the hypotheses of `TwistedFreeRepresentableDiscrete`, the theorem can
therefore supply its eventual-equivariance input for any monomorphic represented
object, including analytic domain inclusions. It does not address general
quasi-étale structure maps.
