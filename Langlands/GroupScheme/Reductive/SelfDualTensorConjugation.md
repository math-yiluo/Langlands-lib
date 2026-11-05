# Conjugation maps from actual self-dual tensor squares

This internal adapter converts a supplied actual tensor-square intertwiner
into a conjugation map when the auxiliary representation has a supplied
invertible actual self-duality map. It works over a field of arbitrary
universe `u`, with finite coordinate types. The acting group is affine for the
conjugation-map construction.

`Intertwines.tensor` proves that the Kronecker matrix of two rectangular
actual intertwiners intertwines the corresponding actual tensor
representations. It uses the existing tensor coefficient formula, entrywise
scalar extension and multiplication of Kronecker matrices, on every affine
test algebra.

For an invertible matrix `D`, `selfDualTensorCoordinates D` is the invertible
Kronecker matrix of the identity with `D`. If `D` intertwines `σ` with its
actual dual representation, this matrix intertwines `σ.tensor σ` with
`σ.tensor σ.dual`. The proof tensors the identity intertwiner with the
supplied self-duality intertwiner. Its invertibility ensures that it preserves
nonzero tensor vectors: applying its inverse to a zero image gives a zero
source.

`ConjugationLinearMap.ofSelfDualTensorIntertwiner` composes a supplied
intertwiner from `ρ` to `σ.tensor σ` with this coordinate change and invokes
`ofTensorIntertwiner`. The result satisfies the unchanged conjugation
equivariance equation on every scheme test. Its final lemma identifies
nonvanishing of the resulting matrix at any base-field vector with
nonvanishing of the original supplied tensor-square image.

The provenance is internal: existing tensor representation coefficients,
Kronecker matrix identities, invertible coordinate changes and the
tensor-dual-to-conjugation adapter. The self-duality intertwiner and
tensor-square map remain explicit data. This module constructs neither a
Steinberg representation nor those data, proves no irreducibility or
exhaustion result, and does not by itself prove
`SimplyConnectedPositiveCharConjugationMapStatement`.
