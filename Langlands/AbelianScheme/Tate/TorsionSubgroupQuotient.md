# Quotients of closed subgroups of actual torsion kernels

This is an internally derived adapter for commensurable lattice realization.
It uses the published actual group-scheme kernel and finite étale quotient
interfaces, Worker 1575's reverse-map construction, and the full Tate
reverse-image calculation. No external literature theorem is asserted here.

Let `A` be an actual abelian scheme over an arbitrary scheme `S`, let `N` be
a natural number, and let `H` be an actual finite étale commutative group
scheme over `S`. Suppose an actual group-scheme map `i` from `H` to the
kernel of multiplication by `N` is a closed immersion.
`ofTorsionSubgroup A N H i` composes this inclusion with the canonical
kernel inclusion to give a `FiniteEtaleSubgroup A`. Closedness follows by
composition of closed immersions. `ofTorsionSubgroup_annihilated` proves
that the composite subgroup inclusion followed by the actual abelian-scheme
map `N • id` is zero. The proof identifies this map with group-scheme
multiplication, uses the cartesian kernel square, and the uniqueness of the
map to the terminal object. No positivity condition on `N` is required.

For an arbitrary finite étale subgroup `K` and supplied actual quotient
data `D`, `comp_eq_one_iff_exists_inclusion` identifies the kernel on points
over every test scheme `T`: a point of `A` maps to the unit under the
quotient if and only if it comes from a point of `K`. The proof uses the
actual quotient-kernel isomorphism and the kernel's point equivalence.
`levelMap_eq_zero_iff_exists_inclusion` is the same equivalence for a point
of any natural torsion level, with the published additive conventions.

For a positive full index `n`, assume the actual subgroup is killed by
`n.val`. `exists_map_inverseMultiple_iff_exists_inclusion` states that an
integral full Tate family of `A` belongs to the image of the actual reverse
map `D.inverseMultiple n.val hK` if and only if its `n`-coordinate lies in
the point image of `K`. It uses the two integral composite identities of
the reverse map, converts their multiplication maps using
`Tate.groupHom_nsmul_id`, and applies `exists_map_reverse_iff` followed by
the quotient-kernel comparison above. The full index predicate is exactly
`fun _ => True`, and the test scheme remains arbitrary.

This adapter assumes the subgroup, and the image lemmas assume quotient
data. It neither constructs a subgroup from invariant geometric points nor
claims the prescribed-lattice realization theorem. Those geometric and
lattice-comparison obligations remain in the parent proof.
