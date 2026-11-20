# Number-field lifting for central norm-one torsion kernels

Let `B/F` be an extension of number fields and let a central
isogeny over `F` have kernel isomorphic to the `n`-torsion of the
Weil norm kernel for `B/F`, with `n > 0`. Assume that `B/F` is
quadratic or that its degree is coprime to `n`.
`numberFieldNormOneKernelLifting` lifts an everywhere locally
trivial natural cocycle on a finite Galois cover of `F` to the
source of the isogeny after a finite Galois refinement.

First enlarge the coefficient field to contain `B` and refine
further to lift every coefficient point. The tensor-unit class
of the central defect vanishes, and after a further finite Galois
refinement there is a tensor-unit primitive killed by `n`. Its
norm is a scalar Kummer cocycle because the differential has
norm one. In the quadratic case the scalar radicand is a norm
modulo powers by local primitive comparison and norm descent.
In the coprime case Bézout gives the same norm condition directly.
Use it to correct the primitive to norm one. The actual kernel
point equivalence and central lifting criterion then give the
lift of the entire natural cocycle. Composing the coefficient
maps gives a refinement of the original cover.
