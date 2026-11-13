# Matrix coordinates on the Lie algebra of the special linear group

Helper module for the proof of
`Langlands.GroupScheme.SpecialLinearSimplyConnectedPinningStatement`. Author: Worker 61
(Task 5703). It gives the Lie algebra of the Library's special linear group scheme
`SpecialLinear.groupScheme n R` coordinates: every element is a trace-zero `n × n` matrix,
and every trace-zero matrix occurs. Here `n` is a finite index type with decidable
equality. All declarations are in namespace `Langlands.GroupScheme.SpecialLinear.FinSucc`.

The Lie algebra is the Library's `lieKernel (groupScheme n R) A`. Its elements are the
`DualNumber A`-points of the group that reduce to `1` modulo `ε`. The coordinates come from
the inclusion `inclusion n R : SL_n ⟶ GL_n` and the published dual-number coordinates of the
Lie algebra of `GL_n` (`GeneralLinear.DualNumber` in `Lie.GeneralLinearAdjoint`).

## Dual-number determinants

These lemmas hold for any commutative ring `A`. Here `epsilonMatrix Y` is the dual-number
matrix `εY` of the Library.

- `det_one_add_epsilonMatrix`: `det (1 + εY) = 1 + ε tr Y`. Proof: Mathlib's
  `Matrix.det_one_add_smul` expands the determinant of `1 + εY` to first order, and the
  second-order term vanishes because `ε² = 0`.
- `epsilonMatrix_eq_zero_iff`: `εY = 0` if and only if `Y = 0`.
- `det_one_add_epsilonMatrix_eq_one_iff`: `det (1 + εY) = 1` if and only if `tr Y = 0`.

## Affine points

- `affinePointsEquiv_inclusion`: on affine points, composing with `inclusion n R` is the
  map `Matrix.SpecialLinearGroup.toGL` from `SL_n(S)` to `GL_n(S)`. This is the Library
  lemma `Corepresented.groupSchemeMap_affinePoints`.

## Lie coordinates

Let `A` be an `R`-algebra.

- `lieMatrix : Additive (lieKernel (groupScheme n R) A) →ₗ[A] Matrix n n A`. It pushes
  an element forward to the Lie algebra of `GL_n` (`Lie.targetMapLinear (inclusion n R) A`)
  and then reads off its matrix with the inverse of `GeneralLinear.DualNumber.pointKernelLinearEquiv`.
  `pointKernelLinearEquiv_lieMatrix` records this definition.
- `mono_inclusion`: the inclusion of `SL_n` into `GL_n` is a monomorphism of schemes. Points
  of `SL_n` are determined by their underlying `GL_n` points.
- `lieMatrix_injective`: `lieMatrix` is injective. The push-forward along a monomorphism is
  injective (`Lie.targetMapLinear_injective`).
- `affinePointsEquiv_lieKernel`: the dual-number point of `SL_n` underlying an element `X`
  of the Lie algebra is the matrix `1 + ε (lieMatrix X)`.
- `trace_lieMatrix`: `tr (lieMatrix X) = 0`. That matrix `1 + ε (lieMatrix X)` lies in
  `SL_n`, so the trace vanishes by `det_one_add_epsilonMatrix_eq_one_iff`.
- `exists_lieMatrix_eq`: every trace-zero matrix `Y` is `lieMatrix X` for some `X`. The
  matrix `1 + εY` has determinant one and so defines a dual-number point `p` of `SL_n`. Its
  image in `GL_n` is the published point `pointUnit Y`, which reduces to `1`. The inclusion
  is a monomorphism, so `p` reduces to `1` and lies in the Lie kernel. Its coordinate
  matrix is `Y`.

## Provenance

The Lie algebra of `SL_n` is the algebra of trace-zero matrices. This is standard, and the
proof here is the usual dual-number computation `det (1 + εY) = 1 + ε tr Y`. The module was
written for this project, after the Library's coordinates for the Lie algebra of `GL_n`.

The `FinSucc.lieMatrix` compatibility definition reuses
`SpecialLinear.lieMatrix` from `GroupScheme/SpecialLinearTorus`. It is the
same inclusion into the general linear Lie algebra followed by the same
dual-number matrix coordinates.
