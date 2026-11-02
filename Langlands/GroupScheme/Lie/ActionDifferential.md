# Differentials of actual automorphic group-scheme actions

The construction differentiates the existing `AutomorphicAction H U` on the
actual kernel of `U(A[ε]) → U(A)`. Its value is the original action at the
constant inclusion of `h ∈ H(A)`. The inverse is the action of `h⁻¹`.
Naturality of the original scheme morphism proves preservation of the kernel,
compatibility with all test-algebra maps, and compatibility with epsilon
scaling. The established affine-kernel module law then gives a linear
automorphism and a homomorphism from `H(A)` to those automorphisms.

This is an internal construction derived from `Lie.Adjoint` and
`AutomorphicAction`; it is not an additional structural assumption. No
smoothness, finite-dimensionality, splitness or characteristic restriction is
used. `differential_conjugation` identifies it with the published adjoint
endomorphism. Consequently normalized subgroup conjugation retains orientation
`h*u*h⁻¹`. Restriction along an actual group-scheme morphism commutes with the
construction.
