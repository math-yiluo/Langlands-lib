# Affine roots under actual cross-torus apartment transport

Author: Worker 118.

Take the same arbitrary-field commuting square of actual isomorphisms
`e : S ≅ S'`, `f : G ≅ H` and inclusions `i`, `j` as in
`CrossTorusApartment`. Assume both underlying inclusions are monomorphisms,
both ambient structural morphisms are affine, and supply
`D : KPApartmentData i ω`. All constructions use the apartment of the
previously constructed transported data, with the unchanged function `ω`.

`D.affineFunctionalTransportEquiv e f h` is a real linear equivalence of the
entire spaces of affine real functionals. It precomposes by the inverse of
the actual apartment affine equivalence, using Mathlib's `AffineEquiv.congrLeftₗ`.
The value at a transported point equals the original value. Its derivative
on a transported reduced translation vector equals the original derivative.
Together with the existing actual root-form identity, this preserves and
reflects the condition that a functional has the derivative of a specified
relative root. Adding any fixed real constant commutes with transport.

For every character and every affine functional, the actual ambient
rational-point map preserves and reflects membership in the original affine
root group. This follows directly from its definition as the intersection
over all apartment points, the point bijection, and the pointwise filtration
identity. Passing to the same positive real constant shifts proves the
corresponding statement for the strict group `U_{ψ+}`. Surjectivity of the
actual point map gives equalities of the entire subgroup images for both
groups. These results require no derivative condition on the functional.

The actual map also preserves the double-root group, including its defining
convention of the trivial subgroup when twice the character is not a root.
This double-root identity does not require either monomorphism assumption.
Injectivity of the actual point map and its compatibility with multiplication
therefore preserve and reflect the containment test
`U_ψ ⊆ U_{ψ+} · U_{2a}(k)` exactly, including the identity.

It follows that the original linear equivalence of functionals preserves and
reflects both `extendedAffineRoots` and `affineRoots`.
`D.extendedAffineRootsTransportEquiv e f h` and
`D.affineRootsTransportEquiv e f h` restrict that same map to bijections of
the two respective sets. In the extended case, the group-image map is
injective, so inequality of the strict and non-strict groups is reflected.
In the ordinary case, the original double-root containment test is reflected.

The provenance is internal. This unit consumes the existing actual apartment
and root/filtration transports and unfolds the published affine root and group
definitions. It constructs no apartment data, root reflection, affine root
system validity or building instance. Identification with independently chosen
target data, full centralizer V6, topological V7, apartment intersections,
full A2 and general building existence remain separate obligations.
