# Matching the quotient images of cocycle trivializations

The cochain comparison implements the quotient-point step of Milne, *Algebraic
Groups* (2017), Theorem 25.71, printed page 565. It uses the Library's cocycles
on all relative tests and the multiplicative pullback point equivalence.
`quotientPointTranslate` takes a local quotient point and forms its left
translate of the image of the local group points. The set is expressed in the
original quotient on the new base viewed as a test over the original base.

Suppose a quotient cocycle is trivialized by a cochain over the original cover
and the ambient cocycle is trivialized by another cochain over a compatible
cover of the new base. After scalar extension, the two quotient
trivializations have equal coboundaries. Their ratio, with the extended
quotient cochain on the left inverted, agrees on pairs of tests and descends
to a section of the new base when its cover is an effective epimorphism.
If the original base has a quotient point whose image lies in the left
translate of the local group image by this section, multiplication on the
right by the corresponding constant cochains makes the two quotient images
equal. Constant right factors cancel in each coboundary.

For an extension to a complete nontrivially normed field, smoothness makes
the map open on affine points. A left translate of its image is open and
nonempty, so density of the original base points in the quotient supplies the
required point. The proof uses the evaluation topology and compares ring
points with sections of the identity test and with the pullback point
equivalence. It takes the stated density as an input.
