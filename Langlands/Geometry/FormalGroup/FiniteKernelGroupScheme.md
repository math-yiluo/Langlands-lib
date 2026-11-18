# The affine group schemes of represented formal kernels

Let a homomorphism of coordinated formal `O`-modules over a commutative
`O`-algebra `R` have a `FiniteKernelModel`. The model includes a finite
projective coordinate algebra and a natural equivalence from its algebra
homomorphisms to the actual kernel points on each test algebra.

`kernelCommGroupPointFunctor` views the additive kernel modules as
commutative groups. The same coordinate algebra corepresents the
underlying set functor. `FiniteKernelModel.commGroupScheme` applies the
Library's group-scheme construction for a corepresented commutative
point functor. This gives the spectrum of the original coordinate
algebra with a group law induced by the actual point groups.
The structure map is finite by module finiteness and flat by
projectivity of the coordinate algebra.

`affinePointsEquiv` is an additive equivalence with the original
kernel points and is natural in the test algebra. A natural linear
map between two such point kernels induces `commGroupSchemeMap`.
Its action on affine scheme points agrees with the given natural map
under `affinePointsEquiv`.

This is an internal construction from the actual finite kernel models
and the Library's affine group-scheme API. It supplies the commutative
group schemes to which the Library's Cartier character functor applies.
