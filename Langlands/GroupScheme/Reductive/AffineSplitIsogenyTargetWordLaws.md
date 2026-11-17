# Complete target word laws for the actual powered family

This internal supporting statement completes the `TargetWordRelations`
bundle for the actual powered Weyl family over a local coefficient ring.
Its inputs are the original characteristic condition of the root-datum
isogeny, corresponding simple-root supports, and genuine normalized target
data for the transported source words. The actual target torus inclusion
is closed.

The standard A2, B2 and G2 fields were proved in
`AffineSplitIsogenyStandardWordLaws` across all possible scaling patterns.
For the remaining no-cone field, `IsogenyNoConeCommutation` proves that the
corresponding genuine target root parametrizations commute, even when the
target cone contains exceptional roots. Its characteristic-two and
characteristic-three arguments are retained; empty source cone is not
replaced by an empty target cone.

Actual word transport identifies the powered source-indexed Weyl maps with
the root powers followed by the target Weyl parametrizations. Precomposing
the proved commutation with these two power maps establishes the required
no-cone identity. The two exponents may differ.

`targetWordRelations_powered` combines this result with the standard fields.
`PoweredTargetWordRelationsStatement` states the complete result in every
universe, and `poweredTargetWordRelations` proves it. No ambient source
group is required. Common Weyl-conjugation relations, restriction to local
tests of an arbitrary affine base, ambient cell gluing and the final
isogeny theorem remain separate obligations.
