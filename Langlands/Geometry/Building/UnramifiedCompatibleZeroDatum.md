# Zero data compatible with a supplied unramified apartment

This internal construction starts with arbitrary maximal-unramified building
data `B` and arbitrary zero data `E` for the original affine group over
`inertiaFixedField F`, for a nonarchimedean local field `F : Type u`.
It retains the original group and the original apartment data.

`UnramifiedZeroDatum.apartmentCompatibleData` constructs zero data whose
maximal-torus inclusion represents the whole centralizer of `B.i` on every
test scheme. It extends `B.i` to a maximal torus using the published
finite-type maximal-torus extension theorem. The original maximal split
torus witnesses that this maximal torus is maximally split. A finite Galois
splitting field is chosen inside the fixed separable closure. The derived
subgroup, simply connected cover, and both covering maps are copied from
`E`.

The centralizer property follows from the published theorem on maximal
tori containing a maximal split torus in a quasi-split group. Its
quasi-splitness premise is discharged using Henselian discrete
quasi-splitness specialized to the actual maximal unramified field.
No local-field structure on that upper field or additional apartment
axiom is assumed.

`withApartmentTorus` is the resulting datum. Its centralizer property is
exported by `withApartmentTorus_isRepresentedBy`. The equalities for the
derived subgroup, cover and simply connected image are definitional.
`withApartmentTorus_zeroPoints` uses the published unconditional independence
of zero data to identify its zero subgroup with the original `E.zeroPoints`.
The multiplicative equivalence `withApartmentTorusZeroEquiv` preserves every
ambient rational point.

The provenance is internal composition of maximal-torus extension, embedded
finite Galois splitting, Henselian quasi-splitness, the quasi-split
centralizer theorem and independence of zero data. This constructs compatible
choices for later comparisons; it constructs no integral model and does not
prove the host parahoric-model target.
