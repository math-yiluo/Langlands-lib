# Euler-sequence differences and coherent graph comparison

`HasVanishingEulerDifference f M hM L d` means that the `d`th forward
difference (step one) of the actual coherent Euler sequence is zero.

This internal prerequisite derives a comparison identity for the actual coherent
Euler sequences on a proper locally noetherian scheme over a field. For a map
`φ : M → N` between quasi-coherent modules with finite affine sections,
`seq(M) − seq(N) = seq(ker φ) − seq(coker φ)`. The proof factors the map
through its actual categorical image, applies Euler-sequence additivity to the
two short exact sequences, and identifies the kernels and cokernels of the
factor maps with those of `φ`.

For modules vanishing outside an irreducible closed `T` of height at most `d`,
an identification on an affine open meeting `T` gives an actual coherent graph.
Its two projection kernels and cokernels have support-height bound strictly
less than `d`. Assuming the vanishing of the `d`th difference for every coherent
module with this smaller support bound, the projection identities imply
vanishing of that difference for `seq(N) − seq(M)`.

The iterated difference commutes with subtraction and annihilates zero because
it is a power of a linear endomorphism of the rational sequence space. The
provenance is internal: the result combines the coherent Euler-sequence API,
abelian image factorization, and the actual coherent graph with its proved
smaller-support errors. It assumes the smaller-support induction hypothesis;
it does not assert the full polynomial theorem or ample positivity.
