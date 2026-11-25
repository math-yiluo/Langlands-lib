# Ambient characters acting on actual unramified induction parameters

This internal module combines the Library's unramified parameter, actual
Levi-normalized induction and fixed compact picture with the ambient
character transport of the standard integral. The coefficient comparison
is the identity linear map, using the product law for character twists.
No original-source assertion or analytic estimate is added.

Fix a smooth character `η` of the ambient group trivial on the source
radical, and an unramified character `τ` of the Levi equal to its restriction.
For every variable unramified parameter `z`,
`ambientParameterCoefficientEquiv` identifies the double coefficient twist
with the parameter `τ * z`. The induced comparison
`ambientParameterInductionEquiv` multiplies values of actual functions by
`η(g)`.

When `η` is also trivial on the target radical, the existing exact-domain
character law and coefficient-equivalence transport prove simultaneous
full-domain convergence at `z` and `τ * z`, with the same quotient measure.
Representability remains in the original coefficient carrier.

For the fixed compact picture, retain the closedness, unimodularity,
compactness, factorization and continuity inputs of that construction.
If `η` is trivial on the chosen compact subgroup, restriction shows the
induced comparison is the identity between the fixed compact vectors.
Injectivity of restriction gives the corresponding identity for extension.
The ambient and coefficient carrier universes remain independent.

Retaining the compatible quotient measure, regular two-sided Haar measures,
closed Levi, ambient Hausdorff topology and squared-modulus compatibility
of the actual target construction, naturality for the identity coefficient
comparison and the ambient character law give
`fullSourceIntertwiner_ambientParameter`. Restriction to the compact subgroup
then proves `standardCompactOperator_ambientParameter`: the two operators
at `z` and `τ * z` are equal on the fixed compact picture. Both full-domain
proofs are displayed in this identity; their equivalence has already been
proved, so the second is not an independent convergence requirement.

Canonical rational scalar invariance and unitary inverse regularity remain
separate obligations.
