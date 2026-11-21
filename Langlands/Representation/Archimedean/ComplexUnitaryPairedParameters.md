# Hermitian pairs of complex inducing characters

`ParameterBlock` encodes a character fixed under Hermitian duality and an ordered pair consisting of a character of positive real exponent and its Hermitian dual. The dual of a singleton has the same data, and the dual of a pair reverses its data.

`exists_parameterBlocks` groups a dual-stable list into such blocks. The proof removes a fixed first character or brings its distinct dual next to it using a list permutation. It cancels the removed entries from the symmetry relation and recurses on the shorter list. The order in the pair is chosen by the sign of the first real exponent. The use of list permutation preserves the multiplicities of all inducing characters.

This is the list calculation for the signature argument on the two-character blocks of the principal series. Its representation-theoretic provenance is Vogan, *The unitary dual of GL(n) over an archimedean field* (1986), Proposition 10.5, p. 476, together with the Hermitian intertwining operators of Theorem 11.5, p. 479.
