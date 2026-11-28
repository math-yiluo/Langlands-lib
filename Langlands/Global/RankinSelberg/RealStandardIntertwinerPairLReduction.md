# Reduction of real pair-factor invariance to positive-weight uniqueness

`realStandardIntertwinerPairLReduction` proves the implication from
`RealPositiveWeightStandardUniqueStatement` to
`RealStandardIntertwinerPairLStatement`. The proof uses the actual
`O(n)`-finite standard modules of the published target. Its provenance is
internal, from the block normalization, the defining Fourier conditions of
the standard modules and the Library's real intertwiner lemmas.

For weight-zero blocks, the proof uses
`realStandardModule_append_flatMap_expand`. For the remaining blocks,
the two position characters and the cutoff for the rotation Fourier
coefficients depend only on the absolute induced weight. Mapping
`RealBlock.positiveWeight` therefore leaves the space of functions equal.
The list normalization also preserves the total rank and gives positive
weights at all induced blocks.

The kernel of the given intertwiner is stable under the compact and Lie
actions. Irreducibility and the nonzero hypothesis make the kernel zero.
The proof transports this injection to the normalized lists using the
equality of the standard modules. Irreducibility transfers by the
surjective identity-on-functions map, since the preimage of any invariant
subspace is invariant. The transported injection is nonzero, and its
invariant range is the entire irreducible target.

Positive-weight parameter uniqueness applied to this bijection identifies
the two normalized lists up to permutation. The normalization and permutation
identities for `realPairLFactor` give the equality of factors in each slot,
and taking their denominators gives the two equalities of the target.

`isIrreducibleGKModule_of_realStandardModule_eq` gives the irreducibility transport for any two equal real standard function spaces, using the identity-on-functions intertwiner described above.
