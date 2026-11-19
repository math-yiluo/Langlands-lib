# Residue maps across compatible local bases

For compatible nonarchimedean local fields \(K\) and \(L\),
`spectralBaseResidueMap` is the map on the residue fields of their
spectral valuation rings induced by the field inclusion. The
spectral base residue degree computes the dimension of that finite
residue extension, and the residue cardinalities satisfy the
corresponding power formula. The same degree computes the
dimension using the intrinsic residue fields.

Let \(X/K\) and \(Y/L\) be algebraic extensions and let \(X\to Y\)
be a \(K\)-embedding compatible with the structure maps. The
spectral valuation rings are the integral closures of their base
integer rings. Thus the embedding carries integers to integers.
If a source integer has valuation less than one, some power of
it is divisible in the source integer ring by a nonzero element
of the base maximal ideal. The embedding carries that base
element into the target maximal ideal. Primality then carries
the original integer into the target maximal ideal. This gives
the local homomorphism needed for `spectralExtensionResidueMap`.

These residue maps are derived from the Library's spectral
valuation and integral closure descriptions. They supply the
actual residue embeddings used in comparing arithmetic Frobenius
under base extension in Serre, *Local Fields* (1979), Chapter XIII,
§3, Proposition 7, printed pp. 193–194. The argument applies in
every characteristic and uses algebraicity of the two upper
fields.
