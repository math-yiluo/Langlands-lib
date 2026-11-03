# Proper unipotent actions with invariant affine neighborhoods

This internal derived module develops a conditional argument from the exact
Kostant–Rosenlicht proposition. The proper solvable fixed-point proposition is
not an input. The construction uses the actual action, its underlying orbit-map
images, and the Zariski topology.

`HasClosedOrbits` says that the orbit image of every rational section is closed.
Over an algebraically closed field, a smooth affine unipotent group action on a
locally finite type scheme has this property if every rational section has an
invariant affine neighborhood and Kostant–Rosenlicht is supplied.

First, a rational point in an orbit closure has an invariant affine
neighborhood. Invariance brings the original section into that neighborhood.
The existing open-embedding closure comparison and Kostant–Rosenlicht then put
the given rational point in the actual orbit image.

For an invariant open containing the original section, the orbit lies in that
open. If the orbit closure extended outside it, its intersection with the
closed complement would be a nonempty closed subset. The Jacobson property
would supply a rational closed point there. The preceding argument puts that
point back in the orbit, a contradiction. Thus the entire orbit closure lies
in each such invariant open. In an invariant affine neighborhood, the same
closure comparison and Kostant–Rosenlicht prove that the orbit is closed.

If the ambient scheme is proper and the acting group is also connected, the
reduced equivariant orbit closure is proper and lies in an invariant affine
neighborhood. Its inclusion in that neighborhood is a closed immersion, so the
closure is affine. A proper affine morphism is finite. The published finiteness
of sections of a finite scheme and the connected smooth finite-target action
theorem give all-test fixedness of a lift of the original rational section.
Equivariance carries fixedness to that section in the ambient scheme.

The final theorem retains the supplied Kostant–Rosenlicht proposition and
invariant affine neighborhoods. It does not prove either input or the flag
step. There is no ambient reducedness assumption, and the field characteristic
and universe are arbitrary.

The main declarations are
`mem_orbit_of_rational_mem_closure_of_invariantAffineNeighborhoods`,
`closure_orbit_subset_invariantOpen_of_invariantAffineNeighborhoods`,
`hasClosedOrbits_of_invariantAffineNeighborhoods`, and
`isFixed_of_invariantAffineNeighborhoods_of_kostantRosenlicht` in the
`Langlands.GroupScheme.SchemeAction` namespace. The last theorem requires an
algebraically closed field, a smooth affine connected unipotent acting group,
a proper ambient scheme, the exact global Kostant–Rosenlicht proposition,
and the stated neighborhood property. Properness supplies local finite type.

This is an internal derivation from the imported orbit, invariant-open,
reduced-closure, finite-section, and finite-target action APIs. In particular,
the lift of the original section through the reduced closed immersion uses
reducedness of the source `Spec k`. The bundled reduced-closure construction
was adapted from Worker 716's draft, as documented in its own pair; this
module imports that construction without changing it.
