# Matrix kernels of actual Lie-element centralizers

This internal module derives the matrix interpretation of the actual all-test
Lie-element centralizer from its dual-number definition. The base is any
commutative ring of arbitrary universe. No smoothness, connectedness,
semisimplicity, finite-type or characteristic assumption is used.

For matrices `M` and `N`, conjugation by the first-order point `I + εM` fixes
the constant tangent lift of `N` exactly when `MN = NM`. The proof uses the
published matrix identity for first-order conjugation. Its correction is the
epsilon matrix of `MN - NM`; equality of matrices in the dual-number ring
detects the zero correction by their second coordinates.

For a monomorphic actual matrix representation `ρ` of an affine group scheme
`G`, `mem_elementCentralizerLie_iff_commute_tangentMatrix` identifies membership
of `Y` in the tangent submodule of the centralizer of `X` with commutation of
`ρ.tangentMatrix Y` and `ρ.tangentMatrix X`. The all-test definition first reduces
to its equation on the affine dual-number test. Monomorphic cancellation and
naturality of actual tangent matrices then reduce it to the matrix identity
above. The monomorphism is of the underlying morphism over the base; a closed
immersion supplies it.

`Lie.tangentCommutator ρ X` is the linear map sending an actual tangent vector
`Y` to `ρ(Y)ρ(X) - ρ(X)ρ(Y)`. Its kernel equals
`Lie.elementCentralizerLie G X` whenever `ρ` is monomorphic. This equality is an
actual equality of submodules of `Additive (lieKernel G R)`, with the raw kernel
identity representing the zero tangent vector.

`elementCentralizerLie_eq_top_iff_commute_tangentMatrix` says that this
centralizer tangent submodule is the whole Lie module exactly when the matrix
of `X` commutes with every actual tangent matrix. Over an arbitrary field,
for an affine locally finite type group, `mem_elementCentralizerLie_comm`
proves that `Y` belongs to the tangent centralizer of `X` if and only if `X`
belongs to the tangent centralizer of `Y`. This last conclusion uses the
published existence of a closed matrix embedding and symmetry of matrix
commutation. It requires no chosen representation as an input.

These computations provide the concrete centralizer comparison needed in the
semisimple-centralizer spanning route. They make no assertion of tangent
spanning, Jordan decomposition, or Cartan generation.
