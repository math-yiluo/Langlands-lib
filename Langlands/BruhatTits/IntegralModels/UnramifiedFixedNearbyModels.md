# Recovered models along fixed descended translation lines

Author: Worker 200.

This internal supporting unit constructs actual recovered models and comparison
maps along every descended translation of a coefficient-fixed apartment point.
It combines `UnramifiedFixedSubsetRecovery` and
`UnramifiedFixerModelComparison`; it is not a new literature transcription.

`RecoveredFixedNearbyModels D f hS x` records a recovered singleton model at
`x`, a recovered model for each two-point set
`{x, D.descentTranslate f hS x v}`, and a compatible full and neutral
generic-identity comparison from each lower source model to the lower target.
Each recovered model includes its actual lower and upper component models,
their compatible unramified recovery, and its exact upper full integral image.
No neutral integral-image formula is asserted.

The entry definition `recoveredFixedNearbyModelsOfVertexInputs` constructs this
package from connected reductivity, the supplied upper maximal split torus and
apartment with its integer-valued centralizer compatibility, a lower split torus
mapping to the upper torus, and a coefficient-fixed point. Five global inputs
remain explicit:

- vertex one-stabilizer maximal boundedness;
- existence of maximal-bounded integral models;
- smooth intersection;
- unramified smooth-model descent;
- unramified smooth Hom extension.

The singleton is chosen by `recoveredFixedPointModelsOfVertexInputs`.
For every lower vector, `galois_fixed_descentTranslate` proves that the translated
endpoint is coefficient-fixed. The two-point constructor therefore supplies
an actual recovered source. Literal inclusion of the singleton in the two-point
set reverses the full norm-one fixer inclusion. The existing comparison
construction and Hom extension yield the actual full and neutral model map.
Neither a lower building nor full-fixer constancy on facet closures is used.

`source_full_integralPoints_le_translatedFixer` follows from the exact upper
full-image equality: a source integral point fixes both endpoints and hence
fixes the translated endpoint. The endpoints may coincide.

`HasParabolicComparisonsNear` is the remaining geometric condition on the
recorded comparison maps. For each lower vector, it requires a common real
neighbourhood of zero on which the comparison at `t • v` has parabolic
special-fibre image and the exact parabolic reduction preimage.

`parabolicRootComparisonsNear` proves the previously defined nearby integral-root
comparison condition from this geometric condition. In addition it assumes
connected reductivity over the upper field, upper opposite-factor pairs, and
that the torus maps compose to the chosen lower inclusion. It supplies the
actual source, recovery and comparison, then applies the existing root-depth
bound using the translated-endpoint fixer inclusion. It therefore discharges
all the root inequalities required by
`ParabolicRootComparisonsNearDescentTranslations`.

The five global input theorems and the nearby parabolic geometric condition are
not proved here. This unit does not assert the unconditional fixed-point
depth-zero opposite-factor theorem.
