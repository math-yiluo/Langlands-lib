# Base change at a weakly unramified vertical local ring

Worker 594.

`residueTensorBaseChangeEquiv` calculates the residue tensor for
base change along an extension of local rings preserving the
residue field. The input local algebra has maximal ideal generated
by the base maximal ideal. Tensor associativity, the residue
field isomorphism, and the quotient description of the residue
tensor identify the new residue tensor with the residue field
of the input local algebra.

For a finite injective local extension of DVRs with unchanged
residue field and a flat Noetherian local input algebra, the
tensor product is finite over the input algebra. Every maximal
ideal contains the image of the old uniformizer. In the new DVR,
this uniformizer is a unit times a power of the new uniformizer.
So every maximal ideal contains the new uniformizer, and the
residue tensor calculation makes its principal ideal maximal.
The tensor product is therefore local with that maximal ideal.

The new uniformizer is regular by flat base change. If a product
vanishes and the second factor is nonzero, the first factor is
in the maximal ideal. Division by the uniformizer and regularity
show inductively that the first factor is in every power of the
maximal ideal. Krull intersection makes it zero. The tensor
product is thus a Noetherian local domain with a nonzero principal
maximal ideal, so it is a DVR. The new base maximal ideal generates
its maximal ideal.

This is a derived stability result for the local rings at
normalized fibre generic points, which are the local rings used
in Conrad's appendix to Prasad–Yu, *On quasi-reductive group
schemes*, author preprint, Remark A.7 on printed and PDF p. 30.
The registered source is `prasad-yu-2006-quasi-reductive-author-preprint`,
SHA-256 `138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
