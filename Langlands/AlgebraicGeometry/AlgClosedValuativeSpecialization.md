# Specialization from algebraically closed valuative tests

This internal helper adapts Mathlib's
`AlgebraicGeometry.ValuativeCriterion.Existence.specializingMap`.
It records the restricted valuative existence condition used in the proof of
the Library's local-cardinality finiteness statement.

`HasAlgClosedValuationLifts f` quantifies over every algebraically closed field
`K` in the universe of the source and target schemes and every valuation subring
`A` of `K`. A commutative square from `Spec K → Spec A` to `f` must have a lift
`Spec A → X` satisfying both triangle identities.

The theorem `specializingMap_of_algClosed_valuation_lifts` concludes that `f`
lifts specializations. Given `f(x') ⤳ y`, compose the specialization map on
stalks, the stalk map of `f`, the quotient to the residue field at `x'`, and
the embedding into its algebraic closure `K`. Mathlib's
`IsLocalRing.exists_factor_valuationRing` factors this homomorphism locally
through a valuation subring `A` of `K`. Applying the assumed lifting condition
and evaluating the lift at the closed point of `Spec A` produces a
specialization of `x'` mapping to `y`.

The helper assumes no finiteness, separation or etaleness condition. It proves
only the specializing-map consequence of the stated restricted valuative
existence condition; no unrestricted valuative criterion is claimed.
All constructions and the valuation-ring factorization are from Mathlib.
