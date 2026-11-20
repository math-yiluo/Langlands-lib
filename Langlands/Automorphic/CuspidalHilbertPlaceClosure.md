# Invariance of local Hilbert closures

`OperatorRealization.CuspidalHilbertPlaceClosureStatement` uses the actual
adelic action on the Hilbert completion of the form computing the
determinant-band inner product. It takes a cuspidal operator realization
with a specified unitary central character. At a real or complex place,
the source subspace carries the compact and complexified Lie actions
of that place. If these operators preserve the subspace, the restricted
action of the full local general linear group preserves the closure of
its image in the Hilbert completion. At each local compact point the
restricted action agrees with the compact operator on embedded original vectors.

The form-level argument applies `preservesImageClosure_of_coefficients`
to the joint-finite coefficient lifts of the reconstructed completion. The affine matrix
restriction preserves their real analyticity, and the local chain rule
identifies each derivative in direction \(gX\) with a Lie generator acting
on the original vector. Each component contains a compact representative.
At that representative the action on the original vector is the original
compact action, by the place-inclusion identity and the completed compact
operator comparison. These facts supply the hypotheses of the coefficient
vanishing argument. The general lemmas first work with a completion
carrying these comparison data and then specialize to the reconstructed
action, whose differential is the original enveloping action.

This result is derived from the Library's adelic completion, place
restrictions, and Hilbert orbit coefficients. It supplies the invariant
closed local spaces for the smooth Whittaker comparison.
