# Ordered residues of the integral Harris source

This internal comparison uses the actual Harris pairing lattice, its
finite-adelic integral span, and the quotient by `m`-multiples in
`HarrisIntegralSourceCongruence`. It supplies source coordinates for the
comparison with ordered finite torsion levels. It makes no assertion about
the existence or representability of the moduli problem.

`harrisIntegralAdeleResidue` is reduction at a positive integer `m` in the
actual integral rational adeles, transported through the integral ring
equivalence of `RationalProfiniteIntegerAdeleComparison`. It is surjective
because the projection of a profinite residue family at `m` is surjective.
Its zero fibre consists exactly of multiples of `m`. To prove the nontrivial
direction in the residue limit, if the `m`-residue of `x` is zero, take the
least nonnegative representative of `x` at `m k`, divide it by `m`, and take
its class modulo `k`. The representative is divisible by `m`. For `k | k'`,
reducing the representative at `m k'` modulo `m k` and then dividing by `m`
gives the same residue modulo `k` as division first. These classes therefore
form a coherent family `y`, and multiplication by `m` recovers `x` on each
coordinate. Conversely an `m`-multiple reduces to zero at `m`.

`harrisIntegralSourceAdelicBasis` extends the finite integer basis of the
actual lattice first to the rational source and then to the finite adeles.
Its vectors span the existing integral adelic span over the integral adeles:
each vector is a tensor of a lattice vector, and the integer basis expansion
of any lattice vector lies in their span. The actual span consists exactly
of vectors whose adelic basis coordinates are integral. One direction is
closure under integral linear combinations; the other uses the finite basis
expansion. `harrisIntegralSourceCoordinates` restricts the basis equivalence
to identify that span with tuples of integral adeles.

`harrisIntegralReducedSourceCoordinates` reduces each integral coordinate
using `harrisIntegralAdeleResidue`. The resulting coordinate map is
surjective and kills exactly `m` times the integral span, by the scalar
kernel computation in each coordinate and the integral basis equivalence.
Its quotient lift is thus an additive equivalence from the *actual* source
quotient to `Fin (Module.finrank ℤ L) → ZMod m`. The formula on quotient
representatives is `harrisIntegralReducedSourceCoordinates_mkQ`.

The order of the coordinates comes from the chosen finite integer basis.
This module does not identify its rank with the dimension parameter of an
abelian family or give a basis of geometric torsion without the Harris frame
comparison. It does not yet prove cofinality of the principal congruence
subgroups.
