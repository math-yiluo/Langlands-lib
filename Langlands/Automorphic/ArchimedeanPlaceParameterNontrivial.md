# Nonvanishing of the standard modules in archimedean place parameters

`Langlands.Automorphic.realStandardKFinite_ne_bot` proves
`realStandardKFinite n ds ≠ ⊥` when `realRank ds = n`.
`Langlands.Automorphic.complexStandardKFinite_ne_bot` proves
`complexStandardKFinite n ds ≠ ⊥` when `ds.length = n`.
These rank conditions are the ones supplied by the real and complex place parameters.

Both lemmas apply Mathlib's `Submodule.nontrivial_iff_ne_bot` to the carrier
of the submodule. The carriers are definitionally those of the published
`Langlands.Archimedean.realStandardNontrivial` and
`Langlands.Archimedean.complexStandardNontrivial`.

The lemmas are derived interfaces for the Library's place-parameter model.
The real construction evaluates a Gram–Schmidt extension of a block polynomial at
the identity. Its rank-two calculation proves the Fourier vanishing for each
induction block. The complex construction uses bottom-right minors and Gram
determinants to produce a unitary-finite vector with value `1` at the identity.
The paired documentation records the proofs and their provenance.
[RealStandardNontrivialProof](../Representation/Archimedean/RealStandardNontrivialProof.md)
[ComplexStandardNontrivialProof](../Representation/Archimedean/ComplexStandardNontrivialProof.md)
