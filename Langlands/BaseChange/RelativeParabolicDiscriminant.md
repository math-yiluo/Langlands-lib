# Relative discriminants for the actual standard block Levi

Let `B : GeneralLinear.BlockShape n` be an ordered block shape. For a field `K`,
write `G(K) = GL_n(K)` and `M(K) = B.Levi K`, included in `G(K)` by
`B.leviEmbedding K`. The relative Lie quotient in this module is the quotient
of all `n` by `n` matrices by the submodule of block diagonal matrices. It is
`𝔤(K)/𝔪(K)`, not the space of strictly upper blocks alone.

- `Langlands.BaseChange.relativeParabolicDiscriminant B K m` is
  \(\det_K(1-\operatorname{Ad}(m)^{-1};\mathfrak g(K)/\mathfrak m(K))\), for
  `m : B.Levi K`.
- `Langlands.BaseChange.twistedRelativeParabolicDiscriminant B σ m` is
  \(\det_F(\sigma-\operatorname{Ad}(m)^{-1};\mathfrak g(E)/\mathfrak m(E))\),
  for a finite extension `E/F`, an `F`-algebra automorphism `σ` of `E`, and
  `m : B.Levi E`. Here `σ` acts on matrix entries and the adjoint action is
  restricted from `E`-linearity to `F`-linearity before taking the difference
  and determinant. The twisted determinant takes values in `F`, not `E`.

Both definitions take the ordinary linear determinant, without an absolute
value or a square root. They use conjugation by the inverse of the embedded
Levi element for the second term. No regularity or nonvanishing is assumed.
The rank and the two field universes in the twisted definition are free; no
local-field topology, characteristic condition, or cyclic generator
condition is needed to define these endomorphisms or determinants.

## Source and scope

Henniart–Lemaire, *Changement de base et induction automorphe pour* \(GL_n\)
*en caractéristique non nulle*, Mém. SMF 124 (2011), II.4.5: printed p. 86
(PDF p. 94), display before (1), defines \(D_{G/M,\sigma}\); the last display
on printed p. 87 (PDF p. 95) defines \(D_{G/M}\). The ordinary specialization
`E = F`, `σ = 1` is described on printed p. 88 (PDF p. 96). The Lean
constructions are the algebraic part of these definitions, with hypotheses
weakened where no topological or cyclic structure is used. The coordinate
identification and the quotient-map verification below are derived here.

This module does not establish orbital-integral descent (1), the identity
between the twisted discriminant and that of the norm, the identity with a
quotient of Weyl discriminants, or the induced-character formula (3).

## Implementation

`offBlockEntries` restricts to the pairs `(i,j)` for which `B.coordinateBlock i`
and `B.coordinateBlock j` differ. These coordinates are surjective by
extension by zero on the diagonal blocks. `blockDiagonalLieSubmodule` is the
kernel, characterized entrywise by `mem_blockDiagonalLieSubmodule`.
`RelativeParabolicLieQuotient` is the actual submodule quotient, and
`relativeParabolicLieCoordinates` is its linear equivalence to the off-block
coordinate space by the first isomorphism theorem. On a matrix representative,
the equivalence is just restriction of entries.

For `relativeParabolicAdjoint`, the underlying endomorphism on matrices is
the Library's `linearAdjoint` of `B.leviEmbedding K m`. The embedding and its
inverse have zero entries between distinct blocks. Products of block diagonal
matrices remain block diagonal: in an off-block entry of the product, each
summand vanishes on one side or the other depending on the intermediate
coordinate's block. Thus conjugation preserves the kernel, and `mapQ` gives
the induced endomorphism with the asserted action on representatives. Using
`m⁻¹` there is the inverse adjoint action, because `B.leviEmbedding K` is a
homomorphism and `linearAdjoint` is conjugation.

For `relativeParabolicSigma`, the entrywise map sends zero to zero, so its
composition with the quotient map annihilates the block diagonal submodule.
The `F`-linear `liftQ` gives the endomorphism on the quotient. Its value on a
representative is the class of the entrywise transformed matrix, and
`relativeParabolicLieCoordinates_sigma_apply` identifies it with entrywise
`σ` in the off-block coordinates. `finiteDimensional_relativeParabolicLieQuotient`
uses the finite-dimensional quotient over `E` and the scalar tower `F ⊆ E`.
For `σ = 1` the quotient map induced by `σ` is the identity by induction on
representatives. In the self-extension, restriction of scalars does not
change the adjoint endomorphism, yielding
`twistedRelativeParabolicDiscriminant_one`.
