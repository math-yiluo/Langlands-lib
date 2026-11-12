# Scalar substitution in Euler polynomials

For any finite-dimensional complex vector space and endomorphism `A`,
`Langlands.Henniart.Extension.eulerPolynomial_smul` identifies the Euler
polynomial of `c • A` with the Euler polynomial of `A` after substitution
`X ↦ c X`. Evaluation gives the same determinant at every complex value,
so polynomial extensionality proves the identity.

This shared module retains the existing theorem's namespace, statement and
proof from `HenniartArithmeticTwistProof`. Both that arithmetic-twist module
and `ClassField.Global.RelativeWeilUnramifiedTwist` reuse it. There are no
Weil-group or arithmetic hypotheses on this linear-algebra identity.
