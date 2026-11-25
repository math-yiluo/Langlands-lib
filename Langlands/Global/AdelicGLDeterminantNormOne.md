# Norm-one points of the general linear group

The Library defines norm-one adelic points by the kernels of the normalized
absolute values of all algebraic characters. Every rational algebraic
character of `GL_n` is an integer power of the determinant, by
`rationalCharacter_eq_zsmul_determinant`. Evaluating that classification in
adelic matrix coordinates identifies this intersection of kernels with
`AdelicGL.determinantNormOne`, the kernel of the normalized idelic
determinant. The proof includes the case `n = 0`.

`GeneralLinearGroupPoints.normOneAdelicHomeomorph` restricts the published
adelic matrix homeomorphism to these subgroups with their original subtype
topologies. This is a derived comparison between the general algebraic
character convention and the matrix convention used for the adelic twisted
centralizers of rational points of `Res_{L/K} GL_n`.
