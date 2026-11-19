# Normalization of the real pair L-factor

`realBlockNormalize` applies the Library's `realBlockExpand` to a real block and
then replaces each negative induced weight by its positive counterpart using
`ComplexCharacterData.conj`. Thus an induced block of weight zero and exponent
`t` becomes the two real characters with exponent `t` and parities `1` and `0`.
An induced block of nonzero weight retains its exponent and acquires the absolute
value of its weight.

The block factors use the shifts in Knapp's formula (3.6) on p. 404 of
*Local Langlands Correspondence: The Archimedean Case*
(`knapp-1994-archimedean-llc`). The normalization lemmas are derived comparisons
of the Library's `RealBlock.tensor` and `realPairLFactor` formulas. They concern
the entire denominators, so the identities also hold at their zeros.

The proof uses Mathlib's `Complex.Gammaℝ_mul_Gammaℝ_add_one`. Taking
reciprocals gives the product of the two shifted real Gamma factors as the
shifted complex Gamma factor. For a weight-zero block paired with a character,
the two expanded characters have the two distinct parities after twisting.
For a weight-zero block paired with an induced block, the two character twists
have the same shift because the norm removes parity. This shift also occurs
twice in the tensor product of the original induced blocks. Conjugating an
induced block preserves its shift against a character and exchanges the two
absolute weights in the tensor product against an induced block.

The proof writes each pair denominator as a double list product and commutes the
products to apply the block identities. Symmetry follows from interchanging the
two slots, since the weights in an induced pair are the absolute sum and the
absolute difference. The normalization and library permutation lemmas then give
`realPairLFactor_eq_of_normalize_perm` for any two pairs of presentations whose
normalized lists agree up to permutation in the corresponding slots.
