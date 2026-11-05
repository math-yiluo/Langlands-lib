# Geometric subgroup multiplication

This internal construction relates the actual subgroup multiplication morphism
to the actual product action. It combines `SubgroupProductOrbit`,
`SubgroupProductGeometry`, and `SplitUnipotentProductGeometry`; it makes no new
assertion from external literature.

For group schemes `V` and `C` over any scheme, `secondFactorInversionIso V C`
is the isomorphism of schemes over the base sending `(v,z)` to `(v,z⁻¹)`.
It is the tensor product of the identity on `V` and the inversion isomorphism
on `C`. No commutativity is required: inversion here is used as a morphism of
schemes over the base.

`secondFactorInversionIso_hom_comp_orbitMap` identifies its composite with the
identity orbit map for the action
`(v,z) · x = j(v) x c(z)⁻¹` with the original `subgroupMultiplication j c`.
The equality is an equality of morphisms over the base and follows from the
published orbit formula and the group-object inversion law.

`smooth_surjective_subgroupMultiplication_of_lie_dimension` works over an
algebraically closed field in arbitrary characteristic and universe. The
actual group schemes `V`, `C`, and `U` are smooth, affine, and connected.
The map `j : V → U` is a group-scheme morphism; `c : C → U` is a closed
subgroup map. The actual scheme-theoretic intersection
`E = subgroupIntersection j c` is affine and smooth. Both factors are
unipotent in the existing all-test representation-theoretic sense. The remaining
explicit hypothesis is
`Lie.dimension V + Lie.dimension C = Lie.dimension E + Lie.dimension U`.
The conclusion is smoothness and underlying-scheme surjectivity of the
original multiplication morphism.

The proof equips the actual product `V × C` with its smooth affine structure.
Connectedness follows from geometric connectedness of the smooth connected
affine factor `C`. The published product dimension formula converts the supplied
equality into `dim(V × C) = dim E + dim U`. The published product action has
closed diagonal intersection stabilizer and the exact right-coset fiber identity
on every relative scheme test, including nonreduced tests. Product unipotence
and the published unipotent closed-orbit theorem make its orbit closed.
`orbitMap_smooth_surjective_of_dimension` therefore makes the original orbit
map smooth and surjective. Composition with `secondFactorInversionIso` and the
preceding equality gives those properties for the original multiplication.

The theorem retains its dimension and geometric hypotheses explicitly. The
finite-field criterion must derive them from rational-point surjectivity and
the finite split series, and descend the resulting properties from an algebraic
closure. Scheme surjectivity here is not an assertion that points lift on
every test scheme without a cover.
