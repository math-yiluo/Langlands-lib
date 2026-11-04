# Full centrality of descended polynomial norms

This internal module proves that the actual `centralNormHom` from
`PolynomialNormHom` is central in the full scheme-theoretic sense. It retains
arbitrary fields `k, L : Type u`, finite Galois `L/k`, and any affine group scheme
`G/k`. No smoothness, connectedness, commutativity, unipotence, characteristic or
perfection hypothesis is imposed.

`mem_center_of_flat_surjective` is a general test-scheme descent lemma. Given
`q : U → T` flat and surjective and a `G`-point on `T` whose pullback to `U`
belongs to the full center, it proves that the original point belongs to the
full center. For any further test `T′ → T` and comparison point on `T′`, the proof
pulls `q` back to `T′`. Full centrality gives equality of the two products after
that pullback. The projection is flat and surjective, hence an epimorphism of
schemes, and cancellation reflects the equality on `T′`. Thus the conclusion
retains every refinement of the test scheme, including nonaffine tests.

`polynomialCoefficients_faithfullyFlat` identifies the coefficient map
`k[Xᵢ] → L[Xᵢ]`, for any variable type in `Type`, as the algebraic base change of
the faithfully flat field inclusion. Stability of faithful flatness under base
change proves its faithful flatness. `mem_center_of_mapCoefficients` applies the
general test-scheme lemma to the spectrum of that map. These two helpers require
only a field extension; finiteness and the Galois property are unnecessary.

`centralNormPoint_mem_center` uses the existing extension formula: extending the
descended norm gives the product constructed inside the full center. The
coefficient-reflection lemma therefore gives full-center membership of the
descended polynomial point. Finally `centralNormHom_isCentral` rewrites the
underlying morphism of `homOfAdditive` to that point and applies the full center
functor's restriction law. Its conclusion is the unchanged `IsCentral` predicate,
quantifying over all schemes and all points of the source vector group.

`centralNorm` packages the descended point with this proved membership as an
actual full-center point over the base polynomial algebra. `centralNorm_val`
records that its underlying point is exactly `centralNormPoint`.

The provenance is internal. These arguments combine the existing full-center
functor, flat-surjective scheme epimorphisms, faithful flatness and polynomial
base change with the existing norm extension formula. They prove centrality
only. Nontriviality, a nonzero tangent, split-unipotence descent and the full
maximal-torus conjugacy theorem remain separate obligations.
