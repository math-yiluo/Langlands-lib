# The discrete-quotient topology on an actual adic completion

Author: Worker 13.

This internal construction equips the existing Mathlib `AdicCompletion I M`
with the topology inherited from the product of the discrete quotients
`M / I^n M`. The ring, source module, target module, third module in the
composition law, and arbitrary topological source all have independent
universes. All natural exponents, including zero, are retained.

`Reduction I M n` is a type synonym for the actual quotient module with the
discrete topology. `Completion I M` is a type synonym for the actual
compatible-family module. Its additive and linear structures are inherited
from Mathlib. The linear equivalence `toAdicCompletion` is the identity on
these sequences. The synonyms keep the selected discrete-quotient topology
separate from any topology on the initial module or quotient modules.
`quotient` is the original canonical quotient map, typed with this discrete
codomain. `transition h` is the original ideal-power reduction from exponent
`b` to exponent `a` for `h : a ≤ b`, bundled as a continuous linear map.
Continuity follows from the discrete source topology.

`inclusion` is the existing linear inclusion into the product. The topology
on `Completion` is induced along this map, and `inclusion_isEmbedding`
certifies precisely this topology. The completion is Hausdorff and a
topological additive group. `eval` is the actual continuous linear coordinate
map; it is surjective by Mathlib's evaluation-surjectivity theorem.
`continuous_iff` characterizes continuity into this completion by continuity
of every coordinate.

`compatible_isClosed` expresses compatibility as the intersection of the
closed equalizers of reduction and coordinate maps between discrete spaces.
Consequently, when every actual quotient module is finite, the completion is
compact: it is a closed subspace of a product of finite discrete spaces.
No finite-generation hypothesis on the original module or ideal is used.

`reductionMap I f n` is the actual map on ideal-power quotients induced by
`f`, restricted to scalars in the original ring and continuous because its
source is discrete. `map I f` is Mathlib's actual induced completion map for a linear map `f`,
restricted to scalars in the original ring and proved continuous coordinate
by coordinate. Its evaluation formula, identity law, composition law, and
compatibility with the original canonical map are proved.
`of` is the original canonical linear map from the module to its completion.
`of_continuous` proves continuity when every original quotient map into the
discrete quotient is continuous; this continuity is an explicit hypothesis
on `quotient I M n`, including the chosen discrete target topology.

The provenance is internal: the algebraic objects and maps come directly from
Mathlib's pinned `RingTheory.AdicCompletion.Basic` and `Functoriality`, also
used by the published `Langlands.Coefficients.AdicSystem`. The added
topology and proofs use the product, induced, discrete, and closed-subspace
constructions in pinned Mathlib. This is a reusable prerequisite for
topological coefficient systems; no new assertion is attributed to Harris.

This construction does not identify the initial module with its completion.
It does not assert ideal-adic completeness, agreement with an independently
specified ideal-adic topology, continuity of scalar multiplication for a
topology on the coefficient ring, a group action, smoothness, a sheaf
construction, or a cohomological comparison. Those are separate obligations.
