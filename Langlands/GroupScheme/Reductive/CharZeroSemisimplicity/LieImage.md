# Tangent matrices are closed under commutators

Author: Worker 1498.

This module is an internal helper for the proof of
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement`. It shows that the
tangent matrices of a finite matrix representation form a Lie algebra under the
matrix commutator. It also gives one Lie-kernel element that acts as the bracket
for every representation at once.

## Setting

`G` is a group scheme over `Spec k` for a field `k`, with `G.X.hom` affine and
locally of finite type. `lieKernel G A` is the kernel of the reduction
`G(A[ε]) → G(A)` on `A[ε]`-points, with `ε² = 0`. For a matrix representation
`ρ : MatrixRepresentation G n`, `ρ.tangentMatrix A X` is the matrix `M` with
`ρ(X) = 1 + εM`. `ρ.kernelDifferential A` is the same map viewed as an `A`-linear
map on `Additive (lieKernel G A)`.

## Declarations

- `Lie.generalLinear_conjugation_constant`: in `GL_n` over `A[ε]`, the
  conjugate of the constant lift of `N` by the point `1 + εM` is
  `N + ε(MN - NM)`.
- `epsilonCoefficients`: the `k`-linear map taking a dual-number matrix to the
  matrix of its `ε`-coefficients.
- `epsilonPart z`: the `ε`-part of a Lie-kernel point
  `z ∈ lieKernel G (k[ε])`. It applies the inverse of the scalar-extension
  isomorphism `k[ε] ⊗[k] Lie(G) ≃ Lie(G)_{k[ε]}` (`Lie.kernelScalarExtension`),
  then sends `a ⊗ x` to `(snd a) • x`.
- `epsilonCoefficients_kernelDifferential`: for every representation `ρ`, the
  `ε`-coefficients of the tangent matrix of `z` over `k[ε]` are the tangent matrix
  of `epsilonPart z` over `k`.
- `kernelBracket X Y`: the `ε`-part of the conjugate of the constant lift of `Y`
  to `k[ε]` by the point of `X`.
- `tangentMatrix_kernelBracket`: for every representation `ρ`,
  `ρ.tangentMatrix k (kernelBracket X Y) = M N - N M`, where `M` and `N` are the
  tangent matrices of `X` and `Y`.
- `tangentMatrix_commutator_mem`: the commutator of two tangent matrices lies in
  the range of `ρ.kernelDifferential k`.

`kernelBracket X Y` does not depend on `ρ`. So when several representations are
used together, one Lie-kernel element realizes the commutator in all of them at
once. `PairLieAlgebra` relies on this for the block-diagonal pair.

## Proof

`generalLinear_conjugation_constant` is the computation
`(1 + εM) N (1 - εM) = N + ε(MN - NM)` in `GL_n(A[ε])`. The lemma
`matrixUnit_conjugate_constant` provides it.

`epsilonCoefficients_kernelDifferential` is proved by induction on tensors after
writing `z` as the image of a tensor under `Lie.kernelScalarExtension`. On a pure
tensor `a ⊗ x`, the tangent matrix of the image is `a` times the tangent matrix of
`x` mapped to `k[ε]` (`tangentMatrix_naturality`). Its `ε`-coefficients are
`(snd a)` times the tangent matrix of `x`. Sums are additive.

For `tangentMatrix_kernelBracket`, let `Z` be the conjugate of the constant lift
of `Y` by the point of `X`. The point of `X` maps to `1 + εM` in `GL_n`, and the
lift of `Y` maps to the constant lift of `N`. Conjugation commutes with `ρ`
(`Lie.targetMap_conjugation`), so the general-linear computation gives
`ρ.tangentMatrix (k[ε]) Z = N + ε(MN - NM)`. Taking `ε`-coefficients and applying
`epsilonCoefficients_kernelDifferential` gives the claim.
