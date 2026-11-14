# Integral ordered root factors preserving a field-fibre quotient kernel

This internal support unit strengthens integral dynamic root generation by
requiring each integral root factor to remain in a specified quotient kernel
on another field fibre. Work over a local domain `R`, with field `k` selecting
the roots and field `l` carrying the quotient. The integral group is smooth,
affine, and geometrically connected, and a coordinate split torus maps to it.
The `k` fibre has a monomorphic torus map and a relative root system. The
homomorphism from the `l` fibre to a smooth affine group is smooth.

`ExponentRootKernelGeneration` says that any subgroup of actual integral
sections containing every selected integral root subgroup intersected with
the kernel of the composite base-change and quotient point map contains the
integral positive dynamic subgroup intersected with that same kernel.
`exponentRootKernelGeneration` proves this assertion under the stated support
hypotheses. No quotient surjectivity on field-valued points is assumed.

The proof enumerates the indivisible positive roots on the `k` fibre, represents
the corresponding full integral root functors, and uses their integral ordered
product isomorphism. It decomposes an actual integral dynamic section through
that chart. Fixed exponent coordinates transport the enumeration and its ray
disjointness to the `l` fibre. Each reduced coordinate lies in the matching
full root functor there. The smooth quotient coordinate theorem forces its
quotient image to be one when the original section has quotient image one.
The resulting integral factors lie in the assumed subgroup and multiply to
the original section.

This is derived support from the Library's local ordered root charts,
field-fibre root-ray comparison, subgroup base change, and smooth quotient
coordinate detection. It makes no new assertion from original literature
and does not yet identify radical root intersections with Bruhat–Tits fixers.
