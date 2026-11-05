# Galois-stable tensor ideals give ideal-sheaf descent

This internal adapter combines `AffineIdealDescent.ofGlobalIdeal` with
`GaloisIdealDescent.map_groundIdeal_eq`. First, a commuting square of actual
coordinate ring equivalences transports an ideal-extension equality to global
sections. Surjectivity of the coordinate equivalence identifies the extended
ideal with the specified ideal sheaf's global ideal.

`ofGaloisStableTensorIdeal` applies this construction to the contraction of a
coefficient-stable tensor ideal over an arbitrary Galois extension. The result
is actual `DefiningIdealDescent` data. No finite-dimensionality, smoothness or
reducedness assumption is used here. The coordinate-square equality and
coefficient stability are explicit premises; this adapter does not yet prove
them for a unipotent radical.

Worker 1359 authored this adapter; Worker 1370 authored the reused tensor-ideal
and invariant-submodule descent proofs.
