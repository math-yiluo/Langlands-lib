# Finite-type compact representations are admissible

Author: Worker 88. `compactFiniteTypeAdmissible` proves the exact Library
proposition `Langlands.Renard.CompactRepresentation.CompactFiniteTypeAdmissibleStatement`,
the Proposition component of `CompactRepresentationCriterionStatements`.

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.3 Proposition and proof, printed p.90 /
PDF p.96, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The exact target concerns smooth complex representations of a Hausdorff,
locally compact, totally disconnected group, with independent group and
carrier universes. Its finite-type condition is finite generation over the
group algebra, not finite complex dimension. Compactness is precisely the
published compact smooth-dual coefficient predicate.

Give the group its Borel measurable structure and construct a left Haar
measure internally. Choose finitely many group-algebra generators `x_i` of
the representation. Fix a compact open subgroup `K` and its published
projection `P_K`. For each `i`, the helper
`finiteDimensional_span_projectedOrbit` from the coefficient-criterion proof
makes the complex span `E_i` of `P_K(π(g)x_i)`, for `g ∈ G`, finite-dimensional.
Their finite sum `F` is therefore finite-dimensional.

To justify that this sum contains every fixed vector, define the actual
subrepresentation `S` consisting of vectors `y` such that every
`P_K(π(g)y)` lies in `F`. It is the intersection of the inverse images of `F`
under the linear maps `P_K ∘ π(g)`. Stability follows from
`π(g)π(h)y = π(gh)y`. Each generator `x_i` belongs to `S` by definition of
`E_i`. Regard `S` as a group-algebra submodule. Since the `x_i` generate the
whole module, every vector belongs to `S`. Apply its condition at `g = 1` to
a `K`-fixed vector `y`. The projection fixes `y`, so `y ∈ F`. This defines an
injective linear map from the whole `K`-fixed space to `F` and proves its
finite dimension.

Finally, for an arbitrary open subgroup `L`, choose a compact open `K ≤ L`
using the published compact-open cofinality theorem. Its fixed space contains
the `L`-fixed space, so the latter is finite-dimensional as well. Together
with the given smoothness this proves exactly the Library's all-open-subgroups
admissibility predicate. The proof follows the source's finite-generator
argument and uses the separately established projected-orbit finiteness
step. It introduces no measure, unimodularity, countability, irreducibility,
finite-length or additional finiteness premise into the target.
