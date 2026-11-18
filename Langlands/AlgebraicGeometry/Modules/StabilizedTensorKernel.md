# Surjectivity and actual kernels of stabilized tensor generator maps

Let `p : X ⟶ Spec R`, let `M` be an actual module sheaf on `X`, let
`q : E →ₗ[R] (relativeGlobalSections p).obj M` be a supplied actual global
linear family, and let `C` be any base module. This internal unit computes
the actual kernel and surjectivity of the previously constructed genuine
stabilized tensor generator map on every affine open `U`.

`stabilizedKernelModel` is the preimage, under the standard coefficient
tensor/product linear equivalence, of the product of the actual kernel
of `globalFamilyTensorMap p M q U` with the zero submodule of
`Γ(X,U) ⊗[R] C`. It is an actual submodule of the stabilized ambient tensor
`Γ(X,U) ⊗[R] (E × C)`.

`stabilizedTensorMap_eq_zero_iff` proves that the actual stabilized map
vanishes on a tensor precisely when the first tensor component lies in
the original actual generator kernel and the complement tensor component
is zero. Apply the actual biproduct section equivalence to the map and
use the previously proved product formula. The complement component map
is the canonical actual associated-sheaf pullback section equivalence;
its injectivity identifies its zero preimage with zero. The theorem
`stabilizedTensorMap_ker` packages this identity as equality with the
stated actual submodule model.

`stabilizedTensorMap_surjective` proves that a surjective original actual
tensor generator map remains surjective under this stabilization. For a
target actual section, use the actual biproduct section projections,
choose a preimage of the first component under the supplied surjective
map, and take the inverse canonical complement equivalence on the second
component. The standard tensor/product inverse gives a preimage in the
original stabilized tensor. The product formula verifies its image.

The provenance is internal: the already proved actual stabilized tensor
product formula, actual biproduct section equivalence and canonical
complement section equivalence supply all proofs. No finite-projective,
flatness, orbit or Grassmannian hypothesis is imposed. In particular,
this unit does not identify any classified Grassmannian point kernel;
that geometric equality is still required in a parabolic application.
