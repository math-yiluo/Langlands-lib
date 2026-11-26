# Tensor intertwiners with a trivial restricted factor

The coefficient argument is the one used in Bushnell–Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), Proposition (5.3.2), printed pp. 176–177.
The retained source `bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The proof takes a coefficient of an intertwiner by fixing a vector in the right
factor of the source and applying a linear functional to the right factor of the
target. These coefficients separate maps and intertwine the left representations
on any common domain where the right representations are trivial.
If a nonzero full intertwiner of the left factors spans the restricted Hom space,
every coefficient is a multiple of it. A functional taking value one on a vector
in its image then reconstructs the unique right-factor map. The intertwining
identity on pure tensors shows that this map intertwines the right factors.

For the irreducibility theorem, let `a : H →* G` and let `ρ` and `τ` be
finite-dimensional complex representations of `G`. Assume `ρ ∘ a` and `τ`
are irreducible and `τ ∘ a` is trivial. The proof uses the Burnside span theorem
to show that any subspace invariant under `ρ ⊗ τ` is stable under every
endomorphism of the left factor acting on its own. Combining a full tensor action with the corresponding
inverse left operator gives the right action on its own. Burnside's theorem
applied to the right factor then gives stability under all right endomorphisms.
Their tensor products span all endomorphisms of the tensor product. Any such
stable subspace containing a nonzero vector contains every vector, by applying
rank-one operators.
