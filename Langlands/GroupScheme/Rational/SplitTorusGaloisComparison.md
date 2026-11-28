# Comparing a split torus with an absolute pinning

`SplitTorusGaloisComparison` packages the data used for descent of
cocharacter parabolics. For a split torus in a scalar extension to `K`,
it gives an actual root datum for that torus and identifies its root
indices and cocharacter lattice with those of a Galois pinning over
`E`. The identification matches the root evaluations and coroots.
An automorphism of `E` fixing `K` acts on the absolute datum by a Weyl
element. For compatible automorphisms of `K` and `E`, two cocharacters
whose images agree up to the Weyl group after the inverse ordinary
Galois action have rationally conjugate parabolics after Galois
transport of the first parabolic.

`SplitPinning.splitTorusGaloisComparison_of_transport` assembles
these data from a root-pairing equivalence, the kernel condition, and
an explicit transport formula with a rational conjugator and a Weyl
element. The inverse of the contravariant coweight map is the lattice
map from `K` to the absolute pinning. Reflection formulas transfer
Weyl elements between the two data. A rational Weyl representative
then absorbs the extra Weyl element in the explicit formula, giving
the transport criterion in terms of Weyl orbits.

This is the comparison used to pass from a diagram permutation to
rational parabolic conjugacy in the cyclic trialitarian descent.
