# Actual values and formula of the direct natural compact comparison

`compactInducedNaturalEvaluation` constructs a value function together with two
proved identities. Its first identity identifies the value with evaluation of
the directly normalized compact comparison. Its second identity identifies the
same value with the original outer inverse-half character times the normalized
coefficient equivalence applied to the original relative-integral value.
`compactInducedNaturalValue` is the value function in this package.

The source is the original target projection-kernel quotient, the point argument
is in the original target Levi image, and the values belong to the original
source Jacquet quotient. The integral is the same chosen
`D.orbitCompactComparison R`, viewed through `compactOrbitIntegralAbstractFamily`
and evaluated on the existing bundled original smooth stabilizer coefficient.
The direct normalized transport is exactly the construction used in
`compactInducedNaturalEquiv`. The generic package keeps its actual evaluation
identity and formula proof together before represented specialization, so its
`.property.1` and `.property.2` expose these identities without restating their
large action indices in standalone represented theorem headers.

This internal assembly uses `normalizedTransportEvaluation`, whose first proof
is reflexivity and whose second proof is `normalizedTransport_eval`. That lemma
eliminates the inducing-subgroup equality and commutes scalar multiplication
through the coefficient linear equivalence. Restriction to the literal target
intersection copy keeps the coefficient linear map unchanged.

The original represented parabolic triples, topology, stabilizer, smooth source
coefficient, subgroup equality and normalizing character are retained, with
independent group and coefficient universes. The dynamic realization remains
explicit. This file makes no new assertion about the inner integral or its choice
of measures, and proves no equality or standalone evaluation theorem for the
earlier separately assembled `compactInducedNormalizedEquiv`. It supplies no
structural realization, relative-root existence, character detection, actual
target quotient compactness, final endpoint identification or proof of the
unchanged closed local orbit-comparison proposition.
