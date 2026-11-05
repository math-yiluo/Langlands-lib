# Continuous positive cocycles and compact overgroups

`Langlands.Topology.PositiveCocycle H X` is an internal abstraction of the
positive change of a line metric under a group action. Its values are in
`ℝ≥0ˣ`, it satisfies
`c(gh,x) = c(g,hx)c(h,x)`, and it is continuous in the group variable for
each fixed `x`. The group and acted-on set have independent universes.
There is no topology or nonemptiness assumption on the acted-on set.

`preservingSubgroup` is the actual subgroup of elements whose value is one
at every point. The multiplication and inverse proofs use the cocycle
identity directly.

`value_eq_one_of_mem_compact_of_fixed` proves that an element of a compact
subgroup has cocycle value one at each point it fixes. On that point the
cocycle sends its nonnegative powers to powers of the same positive real
number. Continuity bounds all these values on the compact subgroup.
The Archimedean growth of powers gives a value at most one. Applying the
same argument to the inverse gives the opposite bound, so the value is one.
This follows the elementary argument of the existing
`Langlands.Topology.CompactNormCharacter` module with a cocycle restricted
to the fixed point in place of a character.

`compactOvergroup_le_preservingSubgroup` assumes a subgroup `K` preserving
the cocycle and acting transitively on `X`. For `g` in a compact overgroup
`L` and `x : X`, choose `k ∈ K` with `kx = gx`. The element `k⁻¹g ∈ L`
fixes `x`, so the preceding lemma gives value one. The cocycle identity
and preservation by `k` then give `c(g,x) = 1`.

The construction and proofs are internal. They introduce no new external
mathematical input. In the intended integral-model application, the
cocycle would come from a metric on the actual flag line bundle.
This module constructs no flag scheme, line bundle, metric, transitivity,
integral-image comparison, or maximal compact subgroup. Those geometric
inputs remain separate obligations; this is not a proof of the supplied
integral-model maximality statement.
