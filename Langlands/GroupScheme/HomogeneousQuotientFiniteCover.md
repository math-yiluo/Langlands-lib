# Homogeneous quotients from finite affine fppf covers

Let `G` be a smooth affine group scheme over an affine scheme `S`, and let
`i : H → G` be monomorphic with `H` smooth over `S`. Suppose a finite jointly
surjective family of affine schemes `Bᵢ → S` is flat and locally of finite
presentation. If each base-changed subgroup has an actual homogeneous quotient
whose underlying scheme is quasi-affine, `quotientOfFiniteAffineCover` chooses
an actual homogeneous quotient over `S`, smooth over `S` and quasi-affine.

This is a derived adapter. Every given local quotient represents the full
restriction of the canonical coset fppf sheaf by
`HomogeneousQuotientSheaf.representableBy_baseChange`.
`FppfQuasiAffineRepresentabilityDescent.quasiAffineModelOfFiniteCover` supplies
a quasi-affine global representative of that sheaf. Such a scheme is separated
over the affine base. `quotientOfIso` then recovers all homogeneous quotient
fields, including the full right-coset equality criterion on every scheme
test. The published smoothness theorem for actual homogeneous quotients of
smooth groups proves smoothness of the resulting structure map.
