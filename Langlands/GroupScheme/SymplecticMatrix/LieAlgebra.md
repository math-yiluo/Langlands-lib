# Matrix coordinates on the Lie algebra of the split symplectic group

This internal module describes the Lie algebra of the split symplectic group scheme
`SymplecticMatrix.groupScheme l R` (from `SymplecticMatrix.Basic`) by matrices. Here `l` is a
finite index type, `R` a commutative ring and `A` an `R`-algebra. Mathlib's standard form is
`J = Matrix.J l A = [[0, -1], [1, 0]]`. The Lie algebra over `A` is the Library's `lieKernel`.
It consists of the points over the dual numbers `A[ε]` that reduce to `1`.

## Dual-number symplectic matrices

* `J_dualNumber`: `J` over `A[ε]` is the image of `J` over `A`.
* `one_add_epsilonMatrix_mul_J_mul_transpose`: for a matrix `Y` over `A`,
  `(1 + εY) J (1 + εY)ᵀ = J + ε (Y J + J Yᵀ)`. Here `epsilonMatrix Y = εY` is the Library's
  embedding of `A`-matrices as the `ε`-part of dual-number matrices.
* `epsilonMatrix_eq_zero_iff`: `εY = 0` exactly when `Y = 0`.
* `one_add_epsilonMatrix_mem_iff`: `1 + εY` is symplectic over `A[ε]` exactly when
  `Y J + J Yᵀ = 0`.

## Affine points

* `affinePointsEquiv l R S`: points of `groupScheme l R` on the affine test scheme of an
  `R`-algebra `S` are the symplectic matrices over `S`. This is the Library's
  `Corepresented.affinePointsEquiv` for the corepresented functor of `Sp`.
* `affinePointsEquiv_naturality`: these bijections are natural in `S`.
* `affinePointsEquiv_inclusion`: composing with the inclusion `inclusion l R` of `Sp` into
  `GL_{l ⊕ l}` sends a point to the same matrix, viewed in `GL`.

## Lie coordinates

* `lieMatrix : Additive (lieKernel (groupScheme l R) A) →ₗ[A] Matrix (l ⊕ l) (l ⊕ l) A` maps
  a Lie algebra element to its matrix. It is the Library's linear map
  `Lie.targetMapLinear (inclusion l R) A` into the Lie algebra of `GL_{l ⊕ l}`, followed by
  the inverse of the Library's coordinate isomorphism `pointKernelLinearEquiv` for `GL`.
  `pointKernelLinearEquiv_lieMatrix` restates this definition.
* `mono_inclusion`: the inclusion of `Sp` into `GL_{l ⊕ l}` is a monomorphism of schemes.
  The proof compares points with `pointsEquiv_inclusion`.
* `lieMatrix_injective`: `lieMatrix` is injective. This is injectivity of
  `Lie.targetMapLinear` for a monomorphism, together with the coordinate isomorphism.
* `affinePointsEquiv_lieKernel`: the dual-number matrix of a Lie algebra element `X` is
  `1 + ε · lieMatrix X`. Proof: combine `affinePointsEquiv_inclusion` with the Library's
  description `pointUnit_matrix` of the `GL` coordinates.
* `lieMatrix_mul_J_add`: every coordinate matrix `Y = lieMatrix X` satisfies
  `Y J + J Yᵀ = 0`. This follows because `1 + εY` is symplectic.
* `exists_lieMatrix_eq`: conversely, every `Y` with `Y J + J Yᵀ = 0` is `lieMatrix X` for
  some `X`. Proof: `1 + εY` is a symplectic matrix over `A[ε]`, so it is a point `p` of `Sp`.
  Its image in `GL` is the Library's point `pointUnit Y`, whose reduction is `1`
  (`pointReduction_pointUnit`). Since the inclusion is a monomorphism, `p` itself reduces to
  `1`. So `p` lies in the Lie kernel, and its coordinate matrix is `Y`.

Together, the last two results identify the Lie algebra of `Sp_{2l}` over `A` with the
matrices `Y` such that `Y J + J Yᵀ = 0`, i.e. with Mathlib's `𝔰𝔭`-condition. No assumption is
made on `l` or on the characteristic.

## Provenance

This is the standard matrix description of the Lie algebra of `Sp_{2l}`. The module is
internal: the proofs were written for it from the cited Library results on the Lie algebra
of `GL_n` (`Lie.GeneralLinearAdjoint`) and Lie functoriality (`Lie.Functoriality`).
