# Quotient measures of intertwiners nested through a represented Levi

`realizedNestedQuotientHomeomorph` compares the actual ordered ambient
radical quotient to the inner quotient of a represented Levi. It first
projects to the literal Levi using `nestedRadicalQuotientHomeomorph`, then
uses `ambientEquivQuotient` for the represented rational points.
`realizedNestedQuotientHomeomorph_symm_mk` identifies the inner radical
coordinate of the inverse comparison.

`exists_realizedNestedQuotientMeasure_eq_smul` compares the exact ambient
and inner measures of `pairQuotientMeasure`. The ambient pushforward is
regular and nonzero, and right invariance survives both transports. The
published uniqueness of right-invariant measures on a left quotient
therefore supplies a fixed positive scalar for the two specified measures.
This is the measure comparison used in descending a standard intertwiner
through an intermediate Levi.
