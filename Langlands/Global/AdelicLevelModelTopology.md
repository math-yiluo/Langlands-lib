# Product topology on actual adelic-level model points

Author: Worker 208.

For every actual scheme over an actual arithmetic S-integer ring, this module
defines the topology induced by the original coordinate map to the product of
points of the actual local base changes. The local point topologies are the
independently constructed `schemePointTopology` topologies from `SchemePoints`.
The target carries their dependent product topology.

`curvePlaceLevelModelPointTopology` uses the original
`curvePlaceLevelModelPointMap`, the completed fields at the actual curve
places in S, and the completed valuation rings outside S. Its scalar ring is
the original `curvePlaceSIntegers` subring of F, with the original constant
and diagonal actions. The construction allows arbitrary fields k and F with
an algebra structure, every finite S, and an arbitrary scheme over that base.
It does not assume that F is a global function field.

`numberFieldLevelModelPointTopology` uses the original
`numberFieldLevelModelPointMap`, every infinite completion, the finite
completions at places in S, and the completed integer rings outside S.
Its scalar ring is the original Mathlib number-field S-integer ring.
The finite-place set S may be empty; all infinite places are still present.

Both definitions preserve the actual relative scheme-morphism carriers and
the actual pullback schemes in `AdelicLevelModelPoints`. Neither source
topology is declared as a global instance. In particular, the definitions do
not replace the existing affine evaluation topology or the separate affine
chart construction on scheme points.

The common helper `localModelPointProductTopology` forms the product of the
independent local-model point topologies for an arbitrary family of
topological coefficient algebras. `localProductPointTopology` induces this
topology along the existing `localProductPointMap`. The two arithmetic
`PointTopology_eq` lemmas show that the explicit level coefficient
equivalences pull back this generic induced topology to exactly the
arithmetic topology. They use the already proved identities for the original
arithmetic maps and the composition law for induced topologies.

The three `PointMap_isInducing` lemmas record the defining induced-topology
identity. An inducing map need not be injective. These lemmas do not assert
an embedding, a bijection, or a homeomorphism.

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp.6–8, Theorem 3.6.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
After proving that (3.6.1) is bijective, the source defines its domain
topology by transport of the product topology on the local-model target.
Inducing that product topology along the original map gives the same
construction when the bijection has been proved. Defining the induced
topology before imposing geometric hypotheses is an explicit implementation
extension; it makes no unconditional bijectivity claim.

All rings, schemes and index types lie in an arbitrary common universe u.
No finite-type, quasi-compactness, quasi-separatedness, separatedness,
local-ring or open-unit hypothesis is needed merely to define these
topologies. Their affine evaluation comparison, the finite-type
homeomorphism, functoriality, transition maps, countability, fibre products,
immersion properties, descent, model independence and the global adelic
colimit remain separate obligations. The generic product helper alone does
not establish an arithmetic theorem, and the curve-place version alone does
not identify the conventional global-function-field presentation.
