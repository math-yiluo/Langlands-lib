# Weyl multiplicities of the normalized principal series

Apply `CuspidalSupport.associatedJacquetFiltration` with both block shapes
equal to the upper Borel shape and with the inducing line formed from
`SphericalExistence.blockCharacters`. Each minimal conjugating permutation
is an arbitrary permutation of the diagonal coordinates. The graded
quotient indexed by `w` is equivalent to the line with diagonal character
`borelCharacter F (z ∘ w.symm)`. The integral diagonal acts trivially on
that line. Its generalized weight space is the whole line at that tuple
and zero at any other tuple, where at least one scalar difference is
nonzero.

At every filtration step, `finrank_torusWeightSpace_exact` adds the
weight dimensions of the previous step and the graded quotient. The
finite sum of the graded dimensions equals the weight dimension of the
actual normalized Borel Jacquet module. Reindex the sum by inverse
permutations to identify it with the count in `weylTupleMultiset z`.
Each permutation contributes separately, including when distinct
permutations give the same tuple.
