# Scalar differentiation of a one-slot tensor action

`externalSlot` acts by the local representation in one slot of an indexed tensor product and the identity elsewhere. It is the restriction of the external tensor representation along the group inclusion supported in that slot.

`hasDerivAt_externalSlot` starts with the derivatives of scalar evaluations of a curve in the local representation. It proves that the scalar derivatives of the induced tensor curve act by the local derivative in the chosen slot. On a pure tensor, multilinearity gives a linear map from the varying slot to the whole tensor. Composing a scalar functional with this map gives the local scalar derivative. Linearity handles sums and scalar multiples of pure tensors.

This internal result is used to differentiate compact translations in the argument for automorphy of isobaric sums of cuspidal representations at every place (`CuspidalIsobaricAutomorphyStatement`; Getz–Hahn, Theorem 10.7.5). Flath (1979), §2, pp. 180–181 (PDF 176–177), gives the tensor product context. The proof uses the Library's one-slot tensor endomorphism and the usual derivative rules for scalar functions.
