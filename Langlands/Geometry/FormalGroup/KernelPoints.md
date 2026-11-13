# Actual kernels and scalar torsion on formal-module points

Let M and N be the finite-coordinate formal O-modules over R constructed
in `FormalModule`, and let f be an O-linear formal homomorphism. For every
commutative R-algebra A, `Hom.kernelPoints f A` is the actual kernel
submodule of the evaluated O-linear map on nilpotent points. Its elements
are points of M(A) whose image under f is zero. It is not a supplied group,
scheme or representing object.

Naturality of evaluation restricts an R-algebra map to a linear map on
these kernels. The resulting `kernelPointFunctor` is defined on all
commutative coefficient algebras. `kernelι` is its natural inclusion into
the point functor of M. Its composite with f is zero. `kernelLift`
constructs the factorization of every natural linear map annihilated by f;
`kernelLift_ι` and `kernelLift_unique` prove its factorization and uniqueness
properties. The proofs use the universal property of actual linear
kernels and the previously proved naturality of formal evaluation.

For composable f and g, `kernelCompMap` sends a point x of the kernel of
g composed with f to f(x) in the kernel of g. This is a natural linear
map. `nilpKernelPointFunctor` restricts the constructed kernel to the
algebras where a distinguished base element is nilpotent.

`scalarHom M a` is scalar multiplication by a in O. Its evaluated map
is scalar multiplication on M(A). The functor `torsionPointFunctor M a`
is its actual kernel, and `mem_scalarKernel` identifies its points with
the equation a times x equals zero.

This is derived point-functor infrastructure for the formal O-modules in
Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §1, printed
p.108, and for isogeny kernels in Rapoport–Zink, *Period Spaces for
p-divisible Groups* (1996), Definition 2.6, printed p.51. The source
defines an isogeny by an fppf epimorphism and a finite locally free
represented kernel. This module constructs the actual kernel functor
and scalar torsion used in that definition. It does not assert that
these kernels are representable, finite locally free, or of any given
rank. It makes no isogeny, height, p-divisibility or rigidity claim.
