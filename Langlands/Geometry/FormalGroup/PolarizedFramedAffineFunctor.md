# The affine polarized framed class functor

`PolarizedFramedAffinePoint.classFunctor` sends each affine Nilp test
algebra to the classes of actual polarized framed triples. Its map
on a class is the class of the coefficient extension constructed in
`PolarizedFramedAffineBaseChange`. The extension of integral
isometries proves that the map is defined on the quotient.

For the identity and composite laws, `baseChangeIdIso` and
`baseChangeCompIso` use the canonical polarized target isometries.
After reduction, the comparisons on both sides of the framing
square have identity coordinate series. Equality of those series
identifies the comparisons with the ones for identity and
composite pullback of rational sheaf sections. Those pullback laws
give equality of the complete framing sections. The two isometries
then give the functor laws on classes.

This functor uses a fixed polarized residue frame and one finite
coordinate system for each target. It implements the affine
polarized framing conditions of Harris (1997), Appendix, printed
p. 113, before specializing the order and imposing the split
special condition.
