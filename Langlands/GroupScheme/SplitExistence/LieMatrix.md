# Matrix coordinates on the Lie algebra of the Chevalley group

Module `Langlands.GroupScheme.SplitExistence.LieMatrix`, namespace
`Langlands.GroupScheme.SplitExistence`. Internal helper of the proof of the split reductive
Existence Theorem (task 2132924b). It is a direct application of the Library's Lie algebra
interface (`lieKernel`, `adjoint`, `Lie.targetMapLinear`) and of its identification of the Lie
algebra of `GL_n` with matrices (`pointKernelLinearEquiv`).

## Declarations

- `targetMapLinear_adjoint`: for a homomorphism `f : G ⟶ H` of affine group schemes, the
  tangent map `Lie.targetMapLinear f A` intertwines the adjoint action of a point `g` of `G`
  with the adjoint action of `g ≫ f`. The adjoint action is conjugation by the constant point
  in the group of dual-number points. Composition with `f` is multiplicative and sends the
  constant point of `g` to that of `g ≫ f`.
- `isAffineHom_GLk`: the instance that `GL_n` over `k` is affine over `Spec k`. This restates
  the Library's `GeneralLinear.isAffineHom_groupScheme`.
- `ChevGroup.lieMat A`: for a Chevalley group `G` with `G.H` affine over `k`, and a
  `k`-algebra `A`, the `A`-linear map `lieKernel G.H A → Matrix (Fin n) (Fin n) A`. It is the
  tangent map of the inclusion `i : G ⟶ GL_n`, followed by the inverse of
  `pointKernelLinearEquiv`.
- `lieMat_apply`: the matrix of `x` is the first-order coefficient matrix of the dual-number
  point `x ≫ i` of `GL_n`.
- `lieMat_injective`: `lieMat` is injective. The inclusion is a monomorphism (`mono_i`), so its
  tangent map is injective (`Lie.targetMapLinear_injective`).
- `lieMat_adjoint`: the adjoint action of a point `g` becomes conjugation by the matrix of
  `g ≫ i`. This combines `targetMapLinear_adjoint` with the Library's
  `adjoint_pointKernelLinearEquiv`.
- `lieMat_map`: for a `k`-algebra map `f : A → B`, the matrix of the image of `x` is the
  entrywise image of the matrix of `x`. This combines `lieKernelTargetLinear_map` with
  `pointKernelLinearEquiv_naturality`.
