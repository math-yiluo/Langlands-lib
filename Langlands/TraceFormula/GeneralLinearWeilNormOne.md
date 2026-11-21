# Norm-one points in the Weil adelic matrix coordinates

`generalLinearWeilAdelicMap_mem_normOne_iff` compares the actual norm-one
subgroup of `(Res_{L/K} GL_n)(𝔸_K)` with the determinant-norm kernel of
`GL_n(𝔸_L)` under the exact map used by the twisted centralizer statement.

The proof first uses `AdelicWeilRestriction.normOneComparison` for the
Weil comparison. The group-scheme base-change isomorphism preserves this
character-kernel condition in each direction by functoriality. The
comparison `mem_normOneSubgroup_iff_determinantNorm` then computes the last
kernel in matrix coordinates.

`generalLinearWeilNormOneHomeomorph` restricts any topological group
equivalence whose underlying map is this coordinate map. Its hypothesis
on that equivalence is supplied by `GeneralLinearWeilAdelicTwistStatement`.
This derived comparison supplies the norm-one restriction used in the
compact quotient and twisted orbit arguments.
