# Translation invariance of finite orbit means

`Langlands.Compact.orbitMean_apply ρ g v` states that translating the initial
vector does not change its orbit mean. The proof identifies the two orbits
as sets and applies the normalized finite-sum expression. It needs neither
topology nor a finite-orbit hypothesis.

The declaration and proof are moved unchanged from
`Langlands.Representation.Jacquet.ExactProof`. Jacquet exactness and
character-twisted averaging now import this common elementary module.
