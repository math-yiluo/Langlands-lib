# Normalized actual orbit coefficient

This internal derived module identifies the actual nested orbit coefficient after
quotient integration and target normalization with the coefficient for normalized
refined induction. It retains every prime, actual finite p-adic extension, supplied
compatible topology, minimal representative and both complete intersection
refinement triples. Coefficient modules and intertwining maps have arbitrary
independent universes, with no topology or finiteness condition on their carriers.

`refinedIntersectionTransport` is the actual inverse intersection-Levi conjugation
between the supplied source and target refined Levi subgroups. The subgroup
identifications only relabel the same embedded elements. Its map retains the
original linear intertwiner.

`parabolicOrbitNormalizedNestedCoefficient` uses the genuine nested section
quotient action, the complex embedding of the actual radical-to-correction Haar
ratio, and the inverse target half modulus restricted to the full intermediate
subgroup. None of these factors is supplied as a comparison premise.

`parabolicOrbitNormalizedNestedCoefficientEquiv` has the same underlying linear
equivalence as the published nested refined coefficient equivalence. That
previous equivalence intertwines the nested action with normalized source
refined Jacquet pulled back by the full source coordinate and multiplied by
both positive source half moduli. Linearity moves the Haar ratio and inverse
target half outside the map. The proved actual normalization cancellation then
identifies their product with exactly the positive target refined parabolic
half modulus. The remaining action is normalized source refined Jacquet,
transported by inverse intersection conjugation and inflated through the target
refined Levi projection. The conclusion is pulled back along the actual stages
to refined-parabolic equivalence and contains no residual twist.

The map sends each original nested coinvariant class to its refined Jacquet
class. Naturality follows from the published naturality of the same underlying
linear equivalence, for every source intertwining map. These are algebraic
consequences of `ParabolicOrbitNestedAction` and `ParabolicOrbitNormalization`;
no new literature theorem is asserted. This pair does not yet assemble the
compact-induction transport, compact-to-smooth inclusion or the final natural
isomorphism of the host orbit functors.
