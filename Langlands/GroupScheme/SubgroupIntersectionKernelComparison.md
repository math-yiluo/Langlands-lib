# Kernels of restrictions and actual subgroup intersections

Author: Worker 1616.

`kernelCompositeIntersectionIso i d q hd hker` identifies the actual kernel
of `i ≫ q` with `subgroupIntersection i d`, over an arbitrary base scheme.
Here `i : H ⟶ G` is any group-scheme homomorphism, `d : D ⟶ G` is a closed
subgroup, and `q : G ⟶ Q` has
`SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d`. The source
`H` need not be commutative, and no flatness or surjectivity of `q` is
assumed. The comparison respects the inclusions into `H`.

Two elementary range equalities implement the comparison.
`range_subgroupIntersectionFst_eq_comap` shows on every test scheme that
the first projection of the actual pullback has range equal to the
inverse image of `range d` under `i`. Its proof uses the actual pullback
universal property, including both directions of the point comparison.
`range_kernelι_comp_eq_comap` rewrites the full kernel membership equation
and reassociates composition. Under the supplied kernel equality, the
two inclusions represent the same subgroup functor. The published
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives the stated
isomorphism and its inclusion compatibility.

Over a field, `isTorus_kernel_comp_of_isTorus_intersection` transports a
supplied torus property of `subgroupIntersection i d` to the actual
restricted kernel. The version
`isTorus_kernel_comp_baseChange_of_isTorus_intersection` gives the same
conclusion after every field extension in the same arbitrary universe.
It first base changes the torus property, then transports it through
`kernelBaseChangeIso`.

This is an internal transport construction from the named Library
pullbacks, represented subgroup comparisons, and torus base-change
theorems. It asserts no new structural fact about intersections of a
maximal torus with a derived subgroup. That intersection being a torus
remains a separate prerequisite for applying this comparison to a
cocenter quotient.
