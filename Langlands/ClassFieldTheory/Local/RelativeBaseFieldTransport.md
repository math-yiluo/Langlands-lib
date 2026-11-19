# Relative unit cohomology under replacement of the upper base

Let \(L\) and \(E\) be two isomorphic extensions of \(K\) whose
embeddings into a common field \(M\) agree under the isomorphism.
`relativeBaseFieldCohomologyIso` identifies their relative
cohomology of \(M^\times\). The group isomorphism leaves every
automorphism of \(M\) unchanged as a map on \(M\). The coefficient
map is the identity on \(M^\times\).

When \(M/K\) is finite, this reindexing preserves relative
corestriction in positive degree. Both relative automorphism
groups have the same image in \(\operatorname{Gal}(M/K)\).
The Lean proof compares the ordinary transfers along the
identity of the ambient group and then uses the positive-degree
comparison with the Tate transfer. This justifies replacing a
finite separable upper base by its image in a common closure
when implementing the transfer of Serre, *Local Fields* (1979),
Chapter XI, §§1–2, pp. 166–168.
