# Pullback of the actual split tower and its order action

For an affine coefficient map `R → S`, the dual and split comparisons
and the order-equivariance equation take a proof of
`FiniteCartierDualExactnessStatement`. It supplies the reversed short
exact sequences needed to form the actual Cartier dual towers over both
bases, including when `S` is the special-fibre coefficient algebra.

`baseChangeDualIso` compares the pullback of the actual dual tower
with the dual of the pulled-back primal. The finite Cartier comparison
on each level is natural for the primal transfer maps. Since their
duals are the inclusions of the dual tower, the level isomorphisms
form actual tower morphisms in both directions. The inverse identities
hold on every finite level.

`baseChangeSplitIso` combines this comparison with the actual product
comparison. It acts identically on the pulled-back primal and by the
Cartier comparison on the dual factor. The product and dual naturality
laws imply that the endomorphisms of the split order agree under this
isomorphism. This applies to the pullback to the special fibre as well
as to changes of the affine coefficient algebra.

See Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), for the
split product, and Harris (1997), Appendix, printed p. 113 (PDF p. 39),
condition (iii) of C1, for its order-linear rigidifier on the special
fibre.
