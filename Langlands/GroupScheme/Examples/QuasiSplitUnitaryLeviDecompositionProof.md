# Levi decomposition of the quasi-split unitary dynamic parabolic

The theorem `Langlands.GroupScheme.QuasiSplitUnitary.leviDecompositionStatement`
proves the unchanged Library proposition `LeviDecompositionStatement` from
`QuasiSplitUnitaryLeviDecompositionStatement.lean`.
Normalization uses the Library's general dynamic decomposition theorem. For
ordered factorization, the unitary scheme is affine and hence separated. Every
parabolic point has a unique limit `l`, and this limit centralizes the
cocharacter. Thus `g = l * (l⁻¹ * g)`, with the second factor having limit one.
Any other admissible ordered pair has its first factor as the limit of `g`,
so uniqueness of limits determines both factors.

The opposite intersections reduce to the matrix descriptions proved by the
imported `dynamicStatement`: upper and lower triangular matrices meet in the diagonal
matrices, while a lower unipotent upper triangular matrix is the identity.
These calculations use global sections on arbitrary test schemes and impose no
reducedness or characteristic hypothesis.

This is an internal derived proof route. It reuses the Library's general
`Dynamic.Decomposition`, `Dynamic.Uniqueness` and the companion unitary dynamic
computation rather than introducing further assumptions.

The proof imports the published companion theorem `dynamicStatement` from
`Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicProof`; the dynamic
descriptions are proved inputs, not additional hypotheses. The final theorem
retains exactly the quadratic field extension, finite matrix basis and
nonidentity automorphism hypotheses of the target. It uses the full unitary
group, without imposing a determinant-one condition.

The source statement's framework is Milne, *Algebraic Groups* (2017),
Proposition 13.28, printed p.264, and Theorem 13.33(b) and its proof, printed
pp.265–266 (retained PDF pages 280–282, one based). Those pages have been read.
The present proof obtains the same ordered factors using general separated
orbit-extension uniqueness already proved in the Library. It does not require
a smoothness proof and makes no new claim about the `SL₂` example being a
unitary theorem. The retained source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
