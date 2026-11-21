# Finite unramified-twist stabilizers

`Numerical.weilTwistStabilizer K σ` packages the defining predicate of
`Numerical.weilTorsionNumber K σ` as a subgroup of `ℂˣ`. The multiplication
and inverse lemmas for the existing twist equivalences give the subgroup laws.
This is an internal construction for the unramified-descent proof; it does
not change the underlying set or its cardinality.

For a class of rank `k + 1`, a stabilizing twist gives an actual isomorphism
on representatives. Evaluating determinants at the chosen geometric
Frobenius multiplies the old determinant by `z ^ (k + 1)`, where `z` is the
twist parameter. The old determinant is nonzero, so `z ^ (k + 1) = 1`. Thus
the stabilizer embeds in the group of `(k + 1)`st complex roots of unity.
It is finite, contains the identity, and has order dividing `k + 1`.

Finally, every element of the stabilizer is an `f`th root of unity for
`f = weilTorsionNumber K σ`, by Lagrange's theorem. The stabilizer and
`rootsOfUnity f ℂ` both have cardinality `f`, so this inclusion is equality.
All arguments keep field and representation universes independent. This
module does not assert divisibility of the Swan exponent or a stratum count.

The determinant argument is the first observation in the unramified-descent
part of the operator's numerical LLC route note (Proposition `prop:unram` and
its use in `prop:tworeductions`), based on Henniart (1988), Proposition 2.2.
