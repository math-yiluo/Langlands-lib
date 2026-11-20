# Scheme base change of represented formal kernels

Let \(f\) be a formal module homomorphism with a finite projective kernel
model over \(R\), and let \(R \to S\) be a map of coefficient algebras.
`FiniteKernelModel.pullbackIso` identifies the scheme of any finite
kernel model for the coefficient extension of \(f\) with the actual
pullback of the original commutative group scheme to \(\operatorname{Spec} S\).
In particular the new model can be the tensor base change of the old one.

On a scheme test \(T\) over \(\operatorname{Spec} S\), the relative Spec
adjunction recovers the kernel points on the global sections of \(T\).
Restricting the algebra structure of these sections along \(R \to S\)
gives the sections of the same test over \(\operatorname{Spec} R\).
The coefficient kernel comparison identifies the actual formal
kernel points on the two algebras. Composing this identification with
the scheme pullback adjunction gives the multiplicative equivalence
on every test scheme. Naturality in \(T\) yields the scheme
isomorphism and its point formula.

The point interpretation also recovers a map of represented kernel
schemes from its specified natural transformation on the kernel
points of relative global sections. The construction is internal to
the formal kernel representations and applies to arbitrary maps of
coefficient algebras.
