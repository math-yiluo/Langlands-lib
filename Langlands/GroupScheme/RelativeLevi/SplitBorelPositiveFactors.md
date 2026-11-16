# Positive root maps into the actual contracting group

This internal construction works over every commutative ring `R` in arbitrary
universe `u`. It turns supplied positive-weight root maps into actual additive
group homomorphisms to any group scheme `U` representing the dynamic contracting
subgroup. It also proves the ordered-product formula for the positive-coordinate
chart inside `U`, on every test scheme.

The motivation is the ordered positive-root description of the dynamically
constructed group in Conrad, *Reductive group schemes* (2014), Theorem 5.1.13,
pp.143–145. The present construction is derived from the Library's represented
subgroup factorization and the contraction and scheme isomorphism proved in
`Reductive/SplitBorelPositiveIso.lean`. It assumes the supplied root maps,
their torus equivariance, and, for the final isomorphism formula, a big-cell open
immersion. It does not construct those data from reductivity.

`rootPoint_comp_hom` and `orderedProduct_comp_hom` express compatibility of
scalar root points and ordered multiplication with homomorphisms of the target
group. The latter follows by induction on the list of factors.

For a cocharacter `ν`, a root map with strictly positive character pairing
contracts to one. `rootPoint_mem_unipotent` specializes the existing finite
ordered-product contraction to a singleton list. Recovering any point of the
additive group from its scalar coordinate gives `range_root_le_unipotent`,
an inclusion of subgroup functors on all tests, without affineness assumptions
on those tests.

If `j : U ⟶ G` represents the contracting functor, `rootToUnipotent` applies
`SubgroupFunctor.IsRepresentedBy.factorHom` to that range inclusion. The result
is an actual group-scheme homomorphism. Its composite with `j` is the original
root map, and the factorization is unique. The scalar-point formula follows
by composing with `j`.

For a finite positive list, `positiveRootToUnipotent` collects these
homomorphisms in that order. Their ordered product has the original ambient
product after composition with `j`. Monicity of `j` therefore identifies the
lifted positive-product chart with multiplication of these maps inside `U`.
`comp_positiveProductIso_hom` specializes that formula to the scheme isomorphism
from positive-coordinate affine space when `U` is affine, opposite weights are
negative, and the big-cell map is an open immersion.

The chart remains a scheme isomorphism over `Spec R`; no additive group law on
`U` is asserted. There is no field, localness, reducedness, connectedness,
nonzero-ring, or nonempty-root-list restriction. Represented height subgroups,
their vector quotients, and the full split-Borel structural theorem remain
separate obligations.
