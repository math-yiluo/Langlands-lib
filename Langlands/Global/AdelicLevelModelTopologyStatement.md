# Topology comparison for actual adelic-level model points

Author: Worker 208.

`AdelicLevelModelTopologyStatement` has four components, all in an arbitrary
common universe u. It concerns the actual maps and actual scheme-morphism
point spaces from `AdelicLevelModelPoints`, with the explicitly defined
source topologies from `AdelicLevelModelTopology`. Each local-model target
has the product of the independently constructed `schemePointTopology`
topologies on the actual local base changes.

The first two components, `CurvePlaceLevelModelTopologyStatement` and
`NumberFieldLevelModelTopologyStatement`, each assert two facts:

1. For an affine model, the defined level topology equals the independently
   constructed affine evaluation topology on the original level-valued points.
2. For a quasi-compact quasi-separated model, the original coordinate map is
   a homeomorphism from the defined level topology to the local-model product.

The curve-place component allows any fields k and F with an algebra structure,
any finite set S of actual curve places, and every scheme over the original
`curvePlaceSIntegers` subring of F. Its factors are the original completed
fields in S and completed valuation rings outside S. It makes no
global-function-field assertion at this general construction level.
The number-field component allows every number field K and every finite set S
of finite places; every infinite completion is included. Its scalar ring is
the original Mathlib ring of elements integral outside S.

The last two components, `CurvePlaceFiniteTypeLevelModelTopologyStatement`
and `NumberFieldFiniteTypeLevelModelTopologyStatement`, assert the same
homeomorphism for models whose structure morphism is locally of finite type
and quasi-compact, namely finite type. The curve-place component additionally
assumes the compatible rational-function algebra structure, scalar tower and
`FunctionField k F` needed for actual S-integer Noetherianity. Constants may
be arbitrary; neither separability, perfectness nor finiteness of the constant
field is assumed. Neither component assumes that the model is affine,
separated or quasi-separated. Quasi-separatedness is a consequence of local
finite type over the actual Noetherian S-integer ring. Local finite type alone
is not asserted to give a homeomorphism.

This is derived content for Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed pp.6–8, Theorem 3.6 and its
proof. Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
After establishing the bijection (3.6.1), Conrad transports the product
topology from the local-model target. The defined induced topology gives
exactly this topology, and the affine comparison identifies it with the
independent evaluation construction. The compact quasi-separated formulations
and arbitrary-constant extension are explicit implementation generalizations
justified by the separate product-map and arithmetic Noetherianity results.

Empty S is allowed in these construction and comparison targets. Conrad's
nonempty all-place convention and the positive-characteristic global
function-field interpretation remain separate application obligations.
The number-field level always contains all infinite places. No claim of
transition-map openness, functoriality, model independence, model descent,
the global adelic colimit or the algebraic-space comparison is included.
These are proposition-valued definitions; proof publication is separate.
