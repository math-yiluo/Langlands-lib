# Residue-maximal relative tori containing a supplied split torus

This internal construction concerns a smooth affine group scheme `G` over a
Henselian local commutative ring `R`, a field quotient `k` with a surjective
structure map, and a closed homomorphism `s : H → G` from a supplied split
integral torus.

`HenselianTorusLifting.containingMaximalData` chooses an actual commutative
relative torus with a closed inclusion into `G` and a closed factorization
of `s`. Its residue inclusion is a maximal torus of `G_k`. The record
`ContainingMaximalData` keeps these maps and their exact composite equation.

The proof applies the published
`exists_maximalTorus_extension_of_finiteType` to the residue of `s`.
Smoothness of `G` supplies local finite type, and affineness and the split
source property survive base change. The resulting factor into the residue
maximal torus is closed by `IsClosedSubgroup.of_comp`.

The published `HenselianTorusLifting.containingLiftData` then lifts the
containing residue torus with its exact residue inclusion and closed
factorization of the original integral source. The field torus is a relative
torus by `IsTorus.relativeTorus`. The lifted relative torus is made into an
actual commutative group scheme by `RelativeTorus.IsTorus.commGroupScheme`.
Finally `IsMaximalTorus.iso_comp` transports maximality through the lift's
residue source isomorphism.

This is a derived construction from these Library inputs, for arbitrary
universe and characteristic. It assumes no reductivity or connectedness of
`G` and does not assert a building or apartment conclusion.
