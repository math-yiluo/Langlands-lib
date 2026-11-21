# Conjugation of local character values

`HasCharacterValue.conjugate` transports a local value from `g` to `a⁻¹ g a`.
For each Haar measure it pulls the open neighborhood back by conjugation by `a`.
A test function on the pulled-back neighborhood gives a test function in the original
neighborhood by composition with the inverse conjugation. The Library's modular
character and Haar integral formulas give the same nonzero factor for both test
functions. Cancelling that factor proves the local value identity.

This is a derived consequence of the modular formulas in
`Langlands.Representation.Character.ModularConjugationProof` and
`Langlands.HarmonicAnalysis.Distribution.RenardModularProof`. It allows any of the
locally profinite groups in the definition of `HasCharacterValue`.
