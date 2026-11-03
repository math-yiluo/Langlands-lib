# The represented identity subgroup

For any group scheme over an arbitrary base, `bot_isRepresentedBy_kernelUnit`
identifies the actual unit homomorphism with the all-test identity subgroup
and proves that its underlying map is a monomorphism. `range_kernelUnit`
records the range equality. Every map to the trivial group scheme is the
unique terminal map, so its composite with the unit is the identity point.

For a separated group scheme, `kernelUnit_isClosedSubgroup` proves closedness
of the identity section by applying the closed-immersion cancellation theorem
to its composite with the separated structure morphism.

The first and third declarations are moved unchanged from
[WeightSupportVanishing](Rational/WeightSupportVanishing.md); the range
declaration is retained from
[TrivialUnipotentRadical](Reductive/TrivialUnipotentRadical.md).
The reductive and adjoint constructions share these general facts.
All statements retain their original universe and base-scheme scope.
