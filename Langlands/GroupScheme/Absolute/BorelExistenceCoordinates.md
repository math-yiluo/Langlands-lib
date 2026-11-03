# Coordinate kernels for Borel existence

Worker 135.

This internal helper module supplies coordinate-ring tools for the existence part
of Milne, *Algebraic Groups* (2017), Theorem 17.9, printed pp.353–354. Milne chooses
a connected solvable subgroup of largest dimension. Our derived proof route
instead minimizes the finite height of its prime vanishing ideal. The module
does not yet assert existence or conjugacy of Borel subgroups.

For a homomorphism `i : B ⟶ G`, `coordinateKernel i` is the kernel of the actual
map `Γ(G, 𝒪) → Γ(B, 𝒪)`. Smoothness and connectedness make `B` integral by the
published `CharacterLatticeProof.isIntegral_of_smooth`, hence this kernel is
prime. A factorization `i = f ≫ i'` gives reverse inclusion of kernels.
For two closed embeddings into an affine group scheme, equal global kernels
give equal ideal sheaves and Mathlib's closed-immersion kernel criterion makes
`f` an isomorphism, first of schemes and then of group schemes.

The global coordinate ring of an affine group scheme locally of finite type
over a field is noetherian. Mathlib's Krull height theorem makes each prime
kernel have finite height. Its strict height monotonicity shows that if the
kernel height of `i` is no larger than that of an overgroup `i'`, a
factorization between these closed subgroups is an isomorphism. The argument
uses neither a global Krull-dimension bound nor conjugacy. These helpers are
valid over every field, in arbitrary characteristic and universe.

The official Milne errata were read when choosing the proof route; no correction
to Theorem 17.9 was found. The height formulation and the categorical kernel
helpers are derived internal content, rather than statements quoted from Milne.
