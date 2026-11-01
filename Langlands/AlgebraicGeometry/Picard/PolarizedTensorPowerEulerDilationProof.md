# Proof of tensor-power and Euler dilation

`polarizedTensorPowerEulerDilation` proves the complete published proposition
`PolarizedTensorPowerEulerDilationStatement`, with its arbitrary scheme,
module sheaf, endomorphism, field, and natural exponents.

For an actual isomorphism `e : f* M ≅ tensorPow M q`,
`polarizedTensorPowIso f M q e n` first applies the published
`tensorPowIso e n`, identifying the `n`th power of `f* M` with the `n`th
power of `tensorPow M q`. The published `tensorPowMulIso M q n` then
flattens the two tensor powers to `tensorPow M (q * n)`.
Both constructions include zero exponents and respect the trailing
structure-sheaf unit in the published right-associated powers.

`polarizedPullbackTensorPowIso` composes the existing general
`actualPullbackTensorPowIso f M n` from
`ClosedImmersionPullbackAmpleProof` with this powered polarization.
That existing construction applies to every scheme morphism; its use
here requires no closed-immersion hypothesis.

These two constructions prove the first clause of the target. For the
second, `hasFiniteCohomology_of_iso` transports finite cohomology along
the powered polarization in each direction, using its inverse for the
reverse implication. Finally `eulerCharacteristic_eq_of_iso` identifies
the integer Euler values for any two supplied finite-cohomology witnesses.
These are the actual derived cohomology modules over the same field and
structure morphism.

The proof is derived entirely from the published categorical constructions
and Euler isomorphism invariance cited above. It establishes the dilation
step only; the Euler polynomial and native-rank leading-coefficient
comparison are separate obligations.
