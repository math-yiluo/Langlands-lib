# Proof of the algebraic twist laws

`twistAlgebraLaws` proves the entire proposition `TwistAlgebraLaws`, with no
extra hypotheses. The reusable component lemmas are `twist_one`,
`twist_twist`, `twist_inv_twist`, and `twist_twist_inv`.

Representation and linear-map extensionality reduce the equalities
to vector evaluation. The unit scalar acts identically. Associativity of
scalar multiplication identifies an iterated twist with the pointwise product.
The two cancellation lemmas use scalar associativity and the two inverse
identities for the unit `chi(g)` at each group element. The final theorem packages all four
proofs in their stated order.

The proof is internal algebra, not an invocation of Henniart's local Langlands
theorem. Its conventions come from the source cited in `AlgebraStatement.md`.
The target is the statement `Langlands.TwistAlgebraLaws`. Its checked target
fingerprint is
`83101ab2432af94bd866f5011df82322ab9eef571ab0ef217ef9d349e518e99c`.
The imported twist definition is `Langlands.Representation.Twist.Definitions`.
The environment is Lean 4.34.0; Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Native compilation and an axiom inspection
found only `propext` and `Quot.sound`.
