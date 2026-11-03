# Split-torus Lie decomposition from finite coordinates

This internal derived module adapts the universal-point proof in
`Torus.ActionWeightDecomposition` to the natural finite coordinates of the
actual Lie kernel. The individual coefficient maps are unchanged. Finite
support and reconstruction now use `FiniteCoordinateCoefficients`, so no
local finite-type assumption on the acted-on group is required.

The universal differential coefficients satisfy their character equations on
all test algebras. They reconstruct each vector and give singleton families
on pure weight vectors. These facts give an internal direct sum. A split
torus isomorphism transports the decomposition from the standard split torus
to an arbitrary split torus and an arbitrary homomorphism into the acting
group. No injectivity assumption on that homomorphism occurs.
