# The adjoint action at a dual-number point is the bracket, over every test algebra

Module `Langlands.GroupScheme.Lie.AdjointTangentBracket`, namespace
`Langlands.GroupScheme.Lie`. Throughout, `G` is an affine group scheme of locally finite type
over a field `k`, `c : FiniteCoordinates G d` is a natural system of finite coordinates of its
dual-number Lie kernels, and `A` is a `k`-algebra. `Additive (lieKernel G A)` is the Lie algebra
of `G` over `A` (the kernel of `G(A[ε]) → G(A)`), with the Library's bracket
`instAffineKernelLieRing` and `instAffineKernelLieAlgebra`. The module makes these two
instances local under the names `kernelLieRingOfField` and `kernelLieAlgebraOfField`, so that
instance search finds them for every `k`-algebra `A`.

## Declarations

- `adjointKernelDifferential_mulVec_base`: over `A = k`, the tangent matrix
  `(adjointRepresentation c).kernelDifferential k y` acts on the coordinates of `x` as `ad y`,
  that is, it gives the coordinates of `⁅y, x⁆`. This is the Library's
  `adjointDifferentialLieHom_apply_bracket`, written with `kernelDifferential`.
- `coordinateEquiv c A`: the coordinates `c.equiv` over `A`, as an `A`-linear equivalence
  `Additive (lieKernel G A) ≃ₗ[A] (Fin d → A)`.
- `adjointKernelDifferential_mulVec`: the same over every `k`-algebra `A`:
  `kernelDifferential A y *ᵥ coordinateEquiv c A x = coordinateEquiv c A ⁅y, x⁆`. Both sides
  are `A`-bilinear in `(y, x)`. The Lie algebra over `A` is spanned over `A` by the images of
  the Lie algebra over `k` (`kernelScalarExtension`, `kernelScalarExtension_tmul`). On such
  images, the tangent matrix, the coordinates and the bracket commute with the coefficient
  change `k → A` (`tangentMatrix_naturality`, `FiniteCoordinates.naturality`,
  `lieKernelMapLinear_lie`). This reduces the claim to the base field.
- `coordinateMatrix_conjugation_snd`: for `y` in the Lie kernel over `A`, the `ε`-part of the
  coordinate matrix of the conjugation action of `G` at the point `y` of `G(A[ε])` is
  `kernelDifferential A y`. The coordinate matrix is the matrix of `adjointRepresentation c`
  at `y` (`finiteRepresentation_affineMatrix`), and that matrix is `1 + ε · tangentMatrix A y`
  (`affineMatrix_lieKernel_eq`).
- `trace_toEnd_eq_trace_kernelDifferential`: the trace over `A` of `ad y` on the Lie algebra
  over `A` equals `Matrix.trace (kernelDifferential A y)`. The proof computes the matrix of
  `ad y` in the basis given by `coordinateEquiv c A`.

## Provenance

Internal. Over the base field, the identification of the differential of `Ad` with `ad` is
Milne, *Algebraic Groups* (2022), §10d, as recorded for `AffineBracketAdjoint`; this module
extends it to arbitrary coefficient algebras by scalar extension.
