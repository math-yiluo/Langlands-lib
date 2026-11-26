# Arithmetic transport of actual cuspidal contragredients

`CuspidalContragredientArithmeticStatement` says that pullback along a number-field isomorphism carries an actual cuspidal contragredient to a contragredient of the pulled-back realization. It uses the full finite, compact, and archimedean operator actions and permits independent field universes.

`cuspidalContragredientArithmetic` transports the bilinear pairing by composing with the inverse arithmetic image maps on both spaces. The maps preserve the finite and compact actions and carry each real Lie direction through the actual Lie algebra isomorphism and its complexification. They are bijective, so the transported pairing is nonzero. The cuspidal invariant pairing criterion then identifies the transported dual realization as the contragredient. `IsoClass.isGaloisConjugate_contragredient` applies this to the inverse Galois automorphism and uses uniqueness of actual cuspidal contragredients to compare the supplied representatives.

The result is an internal consequence of `OperatorArithmeticTransport` and `CuspidalInvariantPairingCriterion`.
