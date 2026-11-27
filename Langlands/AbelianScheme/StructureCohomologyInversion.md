# Inversion on the low-degree cohomology of the structure sheaf

For an abelian scheme over a field, the multiplication pullback on
`H¹(𝒪)` is the sum of the two projection pullbacks by
`pullStructure_mul`. Pullback along the graph of inversion makes the
multiplication map factor through the affine base, where positive-degree
cohomology vanishes. The projection terms become the identity and the
inversion pullback, so inversion acts as minus the identity.

The degree-two result uses the creation and contraction operators of
`canonicalCARData`. Their degree-one creation images span `H²(𝒪)` by
the bounded creation-contraction result. Creations are cup products in
this degree. The Čech product comparison on a common refinement proves
that inversion commutes with cups, so the two degree-one signs cancel
on every generator. These are consequences of the primitive and
exterior-product descriptions in `CanonicalH1Primitive` and
`DegreeTwoComparisonFinal`.
