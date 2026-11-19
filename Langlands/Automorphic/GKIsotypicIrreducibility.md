# Irreducibility inside an isotypic `(𝔤, K)`-module

The free complex algebra on the compact and Lie generators acts on each
carrier by the lift of the two actions, using `GKModuleDensity.gens`. Free
algebra induction shows that stable complex subspaces are submodules and
that intertwiners are module maps. Thus a simple `(𝔤, K)`-module is simple
over this algebra, and the span of its intertwiner images gives the
corresponding module isotypic component.

The injective place-parameter map pulls that component back to the whole
source. Mathlib's isotypic decomposition gives a direct sum of copies of
the chosen simple module. Take a nonzero coordinate of the specified
vector. A matrix unit copies that coordinate into any other summand and
sets all other coordinates to zero. As a module map, it is compact
equivariant and acts by a scalar on the vector. The original coordinate
forces that scalar to be zero, and the other coordinate would be nonzero.
The index set therefore has one element, and the source is simple.

This is an internal algebraic reduction for the cuspidal application.
Flath's *Decomposition of representations into tensor products*, proof of
Theorem 1 on p. 180 (PDF p. 176), supplies the general isotypy argument in
that application. The matrix-unit argument here is a direct use of
`IsIsotypicOfType.linearEquiv_finsupp` and does not require finite length.
