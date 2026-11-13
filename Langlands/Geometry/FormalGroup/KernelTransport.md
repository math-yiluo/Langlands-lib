# Kernel representations under formal-module isomorphisms

This module constructs the finite kernel representation for a formal
O-module isomorphism and transports kernel conditions along
isomorphisms. All points and kernels are those constructed in
`NilpotentAlgebras` and `KernelPoints`.

`Iso.onAlgebraPoints` is the linear equivalence obtained by evaluating
the isomorphism and its inverse over a coefficient algebra A.
The inverse equations show that every point in its kernel is zero.
`Iso.finiteKernelModel` represents this actual kernel by R itself:
there is a unique R-algebra map from R to A and a unique kernel point.
The natural bijection sends the map to the zero point. The coordinate
module is finite free of rank one. Consequently every isomorphism has
kernel rank one, satisfies the affine fppf lifting condition by using
the identity extension of A, and has height zero.

Consider a commuting square with f : M → N, g : M' → N', and
isomorphisms a : M → M' and b : N → N', satisfying g a = b f.
`Hom.kernelEquivOfIsoSquare` sends a point x killed by f to a(x),
which is killed by g. Its inverse is evaluation of the inverse of a;
injectivity of b verifies the kernel equation. Naturality with respect
to coefficient-algebra maps gives `kernelSetIsoOfIsoSquare`.

`FiniteKernelModel.transport` transports a natural representation
along any isomorphism between the actual kernel functors. It retains
the coordinate algebra, its finiteness and projectivity, and its stalk
rank. Thus `hasKernelRank_iff_of_kernelSetIso` proves that constant
rank conditions depend only on the kernel functor.

To transport the affine local-lifting condition through the square,
first apply b inverse to a target point, lift that point using f, and
then apply a. The square and naturality show that the resulting point
lifts the original target after the same faithfully flat finitely
presented extension. This proves transport of `IsIsogeny` and
`HasHeight`.

These are derived invariance constructions for the finite-coordinate
formulation of Rapoport–Zink, *Period Spaces for p-divisible Groups*
(1996), Definition 2.6 and the following height paragraph, printed p.51.
The source defines height by the rank of the finite locally free
kernel. The proofs here use actual evaluation, Yoneda representation
transport and stalk rank; they do not establish scalar-isogeny
existence, height additivity, quasi-isogeny heights, fppf sheaf
comparison, local gluing, rigidity or moduli representability.
