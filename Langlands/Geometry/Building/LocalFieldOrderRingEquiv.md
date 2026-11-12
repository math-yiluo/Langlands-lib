# Normalized local-field order under valuative ring equivalences

This internal prerequisite for Task 5428 derives invariance of the Library's
normalized integer and real orders from their existing normalization. It adds
no continuity or apartment-axiom hypothesis.

The private algebraic lemma proves that two surjective group homomorphisms to
the multiplicative copy of the integers are equal if they induce the same order
comparisons. Choose an element of first order one. Its second order is a
positive integer c. Comparing every element with the appropriate integer power
shows the second order equals c times the first order. Surjectivity of the
second order forces c to divide one, so positivity gives c = 1.

`fieldOrderUnits_ringEquiv` applies this lemma using
`Plancherel.fieldOrderUnits_surjective`, `Plancherel.fieldOrderUnits_ord`,
`FML.ord_le_ord_iff` and the supplied `IsValuativeRingEquiv`. Casting to the
reals yields `localFieldOrder_ringEquiv`. The definition `localFieldOrderHom`
bundles the existing real unit order as a multiplicative homomorphism using
the integer cast; its additive evaluation is definitionally `localFieldOrder`.
Finally `normalizedIntegerOrder_ringEquiv` uses
`IntegerValuation.order_normalized` to give the exact apartment convention,
with the algebra structure induced by the ring equivalence.
