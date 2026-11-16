# Closedness of finite real conic hulls

This internal helper proves closedness of the conic hull of a finite subset of a
real vector space. It supplies the geometric step in the proof of
`Langlands.GroupScheme.ConvexRootSubsetHullStatement` (Renard V.4.2). It is derived
convex geometry, rather than a separate assertion attributed to Renard.

`PointedCone ℝ E` means a submodule over `Nonneg ℝ`: it contains zero and is closed
under addition and nonnegative real scaling. No condition excluding lines is
assumed. The ambient vector space need not be finite dimensional.

All declarations are in `Langlands.Geometry.FiniteCone`.

| Declaration | Content |
| --- | --- |
| `mem_hull_finset` | Membership is a sum over the generators with nonnegative real coefficients. |
| `exists_positive_relation` | A dependent finite family has a zero relation with a positive coefficient. |
| `mem_hull_erase` | A conic combination over a dependent family can lose one generator. |
| `exists_independent_subcone` | Every point of a finite conic hull lies in the hull of an independent subset. |
| `hull_finset_eq_image` | The hull is the image of the nonnegative coordinate orthant under the finite linear combination map. |
| `isClosed_hull_independent` | The hull of an independent finite set is closed in a Hausdorff real topological vector space. |
| `isClosed_hull_finset`, `isClosed_hull_finite` | The hull of any finite set is closed under the same topological assumptions. |
| `moduleTopology_t2Space` | The canonical module topology on a real vector space is Hausdorff. |
| `isClosed_hull_moduleTopology` | A finite real conic hull is closed in the canonical module topology. |

The implemented proof starts by expressing membership in the hull as
`x = ∑ᵢ fᵢ i` with `fᵢ ≥ 0`. If the generators are dependent, choose a nonzero
relation `∑ᵢ gᵢ i = 0`. Reverse its sign if needed to get a positive coefficient.
Among indices with `gᵢ > 0`, choose one minimizing `fᵢ / gᵢ`; call this minimum
`a`. Replace the coefficients by `fᵢ − a gᵢ`. For positive `gᵢ`, minimality gives
nonnegativity; for nonpositive `gᵢ`, nonnegativity follows from `a ≥ 0`. At the
chosen index the coefficient vanishes. The represented vector stays the same
because the change is a multiple of the zero relation. Strong induction on finite
subsets therefore gives an independent subcone containing each point.

For an independent finite set `t`, the linear combination map from `t → ℝ` is
injective. The nonnegative orthant is an intersection of closed coordinate
half-spaces. Mathlib's `LinearMap.isClosedEmbedding_of_injective`, whose domain is
finite dimensional, shows that its image is closed. The whole hull is the union
over the finitely many independent subsets of the original generators, hence is
closed. Empty generating sets and zero generators are covered by the same proof.

To specialize to the module topology, choose a vector-space basis. The map taking
a vector to all its basis coordinates is injective. Each coordinate is a linear
map to `ℝ`, and is continuous by
`IsModuleTopology.continuous_of_linearMap`. The coordinate product is Hausdorff,
so `T2Space.of_injective_continuous` makes the module topology Hausdorff as well.
The module topology already makes addition and scalar multiplication continuous.
This supplies all hypotheses of the preceding finite-hull theorem without any
finite-dimensionality assumption on the ambient space.

The coefficient-elimination implementation adapts the minimum-ratio argument in
Mathlib's `Analysis/Convex/Caratheodory.lean`, by Johan Commelin and Kim Morrison
(copyright Kim Morrison, 2020; Apache 2.0). That argument eliminates a generator
from a convex combination using an affine relation; here a linear relation is
used and no normalization of the coefficient sum is imposed. The source copyright
and license attribution are retained in the Lean file. The referenced Mathlib
source is from the prepared environment, commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The imports provide the nonnegative-scalar cone, finite sums and spans, linear
independence, vector-space bases, and finite-dimensional closed embeddings. All
proofs use ordinary Lean terms and the standard classical axioms only.
