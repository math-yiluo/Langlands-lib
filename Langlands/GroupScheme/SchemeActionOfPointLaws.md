# Categorical scheme actions from point laws

Worker 1293.

This internal constructor takes one actual morphism `H × X → X` over an
arbitrary base scheme, with identity and multiplication action equations
on every relative scheme test. It returns Mathlib's standard `ModObj H.X X`
structure. This is the categorical structure abbreviated by `SchemeAction`.

The unit law is tested on the universal point of the target over
`1 × X`. The product pairing with the identity group point is the unit map
times X, and the left unitor is the second projection.

For associativity, use the universal three points on `(H × H) × X`.
Their multiplication on the first two factors is the categorical
multiplication times X; the pairing for the iterated action is the
associator followed by the action on the last two factors. The assumed
point equation is therefore exactly the categorical associativity law.
The final projection lemma records that the action morphism is unchanged.

The provenance is internal, from cartesian products and the existing
categorical group and module-object definitions. This constructor supplies
no fixed-point theorem or quotient geometry. Its intended application is
to an independently constructed quotient action morphism whose all-test
identity and multiplication laws have already been proved.
