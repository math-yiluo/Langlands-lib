# Scalar character of a transported complex determinant twist

`Langlands.transportedComplexTwistScalarCharacter` constructs a character
`χ : (Fin E.length → F.Carrierˣ) →* ℂˣ` for the actual transported
representation

```text
transport C E w hw
  (T.leviComplexPowerTwist C (fun k => -v k + I * b k) ω.ρ).
```

Here `ω` is irreducible, admissible and unitarizable, and `hw` is the
supplied Levi-conjugation witness. The character has open kernel in the
topology supplied by `T`, acts by scalars on this representation, and has
real part

```text
j ↦ -(E.size j : ℝ) * v ((blockEquiv hw).symm j).
```

The field and representation universes are independent. The calculation
does not require positive total rank.

The proof obtains the published `UnitaryCentralCharacter` of `ω`. It
pulls that character back along the continuous inverse of the actual
`leviConjugation`, then restricts it to the target block scalars. Multiplying
by the target complex determinant character gives `χ`. The published
`transport_leviComplexPowerTwist` identity reindexes both real and imaginary
parameters by the inverse block bijection and proves the scalar action.

The twist is smooth by `isSmooth_leviComplexPowerTwist_iff`, and transport
preserves smoothness. Continuity of the block-scalar homomorphism follows
coordinatewise from continuity of scalar matrices. The published smooth
scalar-character argument therefore gives the open kernel in the original
topology. The unitary character has norm one. The block-scalar determinant
formula and the complex-power norm identity give the displayed real part;
the imaginary parameters contribute no absolute-value factor.

This is internal derived algebra, adapted by Worker 1008 from Worker 429's
`TransportedTwistScalarProbe` in the task-pinned shared comparison draft.
It specializes the published central-character, group-transport and
complex-twist constructions. Its scalar-character conclusion is used by
the companion cone proof; it asserts no Jacquet occurrence or analytic
exponent estimate.
