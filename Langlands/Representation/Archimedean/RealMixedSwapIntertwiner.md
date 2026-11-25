# The induced-character rank-three unlinked intertwiner

This module constructs an induced-character intertwiner by conjugating
an intertwiner for the reversed character-induced pair. Its existence theorem
`RealMixedSwapTwist.inducedCharacterSwap_unlinked` retains exactly the nonzero
weight, real-exponent order and unlinkedness hypotheses for the original pair.
It concludes
`RealInjectiveIntertwinerExists 3 [induced d, character b] [character b, induced d]`.
There is no extra representation theoretic premise in this theorem.

Write `d′ = reverseInduced d`, `b′ = reverseCharacter d b`, and
`q = mixedSignPower d`. Thus the induction weight is unchanged, both complex
exponents are negated, and the real character receives the sign correction
`q = |d.weight| + 1`. The two equivalences of `RealMixedSwapStandard` send the
orthogonal-finite standard-module spaces for `[induced d, character b]` and
`[character b, induced d]` to those for `[character b′, induced d′]` and
`[induced d′, character b′]`, respectively.

For a complex-linear map `T` from the first reversed space to the second,
`inducedCharacterSwapMap d b T` is the composition of the first equivalence,
`T`, and the inverse of the second equivalence. Both equivalences act on
underlying functions by the same signed reversal. Therefore the conjugation
principle in `RealMixedSwapConjugation` proves compact and infinitesimal
intertwining for the new map whenever `T` intertwines these actions. The common
determinant-sign scalar in the compact action agrees on both sides, and the
common Lie direction is negative transpose. The theorem
`inducedCharacterSwapMap_intertwiner` records this property. The theorem
`inducedCharacterSwapMap_injective` records injectivity by composition with
the two linear equivalences. `inducedCharacterSwap_exists` packages these
facts as transport of an existing reversed injective intertwiner.

To discharge the existence input, `inducedCharacterSwap_unlinked` applies
`RealCharacterInducedUnlinked.injective_unlinked` to `b′` and `d′`.
`reverseInduced_weight` preserves the nonzero-weight hypothesis.
`exponent_order_reverse` turns the original decreasing real-exponent order
into the required order for the reversed pair. `unlinked_reverse` transports
the original mixed unlinkedness. The proved character-induced theorem then
gives the reversed injective intertwiner, and the preceding conjugation
construction gives the claimed map for the original pair.

The proof uses the actual Library function spaces and actions. Its inputs are
the proved character-induced construction, the explicit signed equivalences,
the signed action identities and elementary composition of injective maps.
It introduces no classification or irreducibility assumption and makes no
additional literature claim. Transport through arbitrary surrounding lists is
a subsequent use of `RealInjectiveIntertwinerExists.in_stages`; this module
supplies the rank-three middle map.
