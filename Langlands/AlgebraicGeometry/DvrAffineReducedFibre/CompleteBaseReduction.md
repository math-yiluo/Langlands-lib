# Reduction of the affine reduced fibre theorem to a complete base

`DvrAffineReducedFibreCompleteBaseStatement` is the affine reduced fibre
statement for DVRs complete in the maximal-ideal adic topology and with
algebraically closed residue field. The conclusion keeps the same finite
integral closure and the same all-field reducedness test as
`DvrAffineReducedFibreStatement`.

`dvrAffineReducedFibre_of_completeBase` proves the original statement
from the complete-base assertion. First choose the faithfully flat
complete DVR extension supplied by `exists_completeAlgClosedResidueDvrExtension`.
The base-changed algebra is flat and of finite type, and smoothness of
its generic fibre follows from the injective change of base domains.
Apply the complete-base assertion to this algebra. The resulting
extension is faithfully flat over the original DVR by transitivity.

Associativity of scalar extension identifies the iterated base-changed
algebra with the single base change to the resulting DVR. Both generic
fibres are localizations at the image of its uniformizer. The Library's
integral-closure transfer lemma carries finiteness and the fibre tests
across the algebra isomorphism.

The reduction uses the complete algebraically closed residue base
in Conrad's appendix to Prasad and Yu, *On quasi-reductive group schemes*,
author preprint, pp. 31–32, A.10. The target permits the composite
faithfully flat DVR extension as its witness.
