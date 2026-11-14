# Actual isometry torus weights from rank equal to the Witt index

This internal assembly is a conditional prerequisite for the maximal split torus theorem. The finite support is the support of the actual
universal inverse row action after choosing a split realization of the torus.
The row spaces span and are independent. Transporting a cocharacter through
the chosen isomorphism identifies its weight spaces with the finite sums
selected by pairing with the actual characters of the original torus.

For a closed split torus of the actual isometry group of a nondegenerate
quadratic form, rank equal to the Witt index is an explicit premise. Under that
premise, the proved dimension bound and opposite-weight duality meet the
inputs to `SignedWeightCharacterBasis.exists_characters_of_decomposition`.
The resulting actual independent characters detect cocharacters and give the
signed-pair count with the residual zero-weight dimension. No characteristic
or infinitude hypothesis is used. The geometric rank equality is not proved
in this module.
