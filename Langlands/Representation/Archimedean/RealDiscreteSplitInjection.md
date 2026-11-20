# Injection into the reverse of a real character pair

`Langlands.Archimedean.RealDiscreteSplitInjection.splitInjection` embeds the finite vectors
of a real induction block of nonzero absolute weight into the standard module of its
high/low character pair, within arbitrary surrounding blocks. The exponents of the two
characters are those of `RealInducedCharacter.ca` and `RealInducedCharacter.cb`. Their
signs add to the absolute weight plus one modulo two.

This is an internal construction derived from `RealInducedCharacterMaps` and
`RealCharacterPairReducible`. The low/high pair maps to the induction block and to the
high/low pair. Both Frobenius maps satisfy the tail recurrence. Their symmetry signs
can differ, and on the allowed parity class both multipliers vanish exactly in the
same Fourier window. Fourier uniqueness on the compact group gives equality of the
kernels. The tail map to the induction block has the linear section
`RealInducedCharacter.data_tailInv`. Composing the section with the map to the
high/low pair gives the displayed injection. Descent along the surjective tail map
proves compact and Lie equivariance.
