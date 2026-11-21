# Fixed-factor slices of the cuspidal tensor decomposition

This module gives the algebraic local subspaces used to restrict a global
Whittaker functional one place at a time. It uses the actual tensor
equivalence of `CuspidalPlaceTensorDecomposition` and the transport of
irreducibility and admissibility in `PlaceComponentMinimal`.

Choose an infinite place `i`, a vector `a` in the chosen finite adelic
factor, and a vector `b j` in each chosen infinite place factor. The map
`placeTensorSlice i a b` replaces `b i` with its argument, takes the pure
tensor with finite factor `a`, and applies the tensor equivalence. The
other entries of `b` stay fixed. Linearity follows by taking the linear
map in the single variable `i` of the multilinear pure tensor operation.

`tensorSlice_compact` and `tensorSlice_lie` identify the compact and
complexified Lie actions on the source and on the image, respectively.
The pure tensor nonvanishing lemma gives injectivity when `a` and the
other `b j` are nonzero. Transport from the whole source factor gives
an irreducible admissible range for the actual operators at `i`. Smoothness
of the finite factor gives an open subgroup fixing `a`. A compact open
subgroup inside it fixes the entire slice by the finite action formula
for the tensor equivalence.

`PlaceTensorSliceStatement` collects injectivity, irreducibility,
admissibility, and the common finite stabilizer for the chosen cuspidal
decomposition. It is an internal consequence of the published algebraic
models and is the input for placing these slices in the actual unitary
Hilbert realization. The analytic comparison of smooth vector topologies
and Whittaker restrictions requires further results.
