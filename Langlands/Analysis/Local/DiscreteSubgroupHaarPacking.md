# Haar packing for a discrete subgroup

Let `Γ` be a discrete subgroup of a locally compact Hausdorff topological
group with left Haar measure `μ` on its Borel measurable space.
`DiscreteSubgroupHaarPackingStatement`
selects a compact identity neighborhood `W` inside any prescribed identity
neighborhood such that every compact `D` meets `Γ` in finitely many points,
and
\[
\bigl|\Gamma\cap D\bigr|\ \le\ \frac{\mu(DW)}{\mu(W)}.
\]

The two compact-set measures are finite, and the ratio is taken in the
reals.

Discreteness isolates the identity in an open set. Continuity of
`(x, y) ↦ x * y⁻¹` gives a sufficiently small compact neighborhood `W`
whose pairwise quotients lie in that open set. The translates `γ W`,
for `γ` in `Γ ∩ D`, are therefore disjoint. The intersection is finite
because `Γ` is closed and discrete and `D` is compact. Left invariance
gives each translate the same positive measure, while their union lies
in `D * W`.
