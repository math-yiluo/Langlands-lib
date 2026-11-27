# Identity tangent vectors of `G(F_∞)` as dual-number points: Lie brackets

Module `Langlands.Global.InfiniteAdelicTangentKernelBracket`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`. The notation is that of
`InfiniteAdelicTangentKernel`: `F` is a number field, `G` an affine group scheme over `F` with
`hsmooth : SmoothOfRelativeDimension d G.X.hom`, `G(F_∞)` carries the Library's manifold
structure `smoothChartedSpace F G hsmooth`, and `tangentKernel F hsmooth X ∈ lieKernel G F_∞` is
the dual-number point `a ↦ a(1) + ε D_X a` of an identity tangent vector `X`.

Two brackets are compared.

- On `GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)`: Mathlib's bracket
  of left-invariant vector fields. It is taken for the Library's Lie group structure
  `smoothLieGroup F G hsmooth`, lowered to the smoothness `minSmoothness ℝ 3` that Mathlib's
  instance asks for (`LieGroup.of_le`).
- On `Additive (lieKernel G F_∞)`: the Library's bracket `instAffineKernelLieRing`. It is made a
  local instance through `Lie.kernelLieRingOfField` and `Lie.kernelLieAlgebraOfField` (module
  `Langlands.GroupScheme.Lie.AdjointTangentBracket`).

## Declarations

- `representationEntry F ρ i j`: for a matrix representation `ρ : MatrixRepresentation G (Fin n)`,
  the regular function of `G` obtained by pulling back the `(i, j)` entry function
  `GeneralLinear.entrySection` of `GL_n` along `ρ`.
- `affineMatrix_apply_eq_evaluation`: for every `F`-algebra `C` and `g ∈ G(C)`, the `(i, j)`
  entry of `ρ(g)` is the value of `representationEntry F ρ i j` at `g`.
- `realization F ρ : G(F_∞) →* Matrix (Fin n) (Fin n) (Π_v F_v)`: the representation `ρ` on
  `F_∞`-points, with values in matrices over the real normed algebra `Π_v F_v`.
- `contMDiff_realization_entry`: every entry of `realization F ρ` is a smooth function on
  `G(F_∞)`. At each place it is `placeValue` of `representationEntry`, which is smooth by
  `contMDiff_placeValue`.
- `matrixDifferential_realization`: the entrywise differential at the identity
  (`MatrixCoefficientLie.matrixDifferential`) of `realization F ρ` along `X` is
  `ρ.kernelDifferential F_∞ (tangentKernel X)`, the tangent matrix of `ρ` at the kernel point.
  The `(i, j)` entry of the left side at the place `v` is the derivative of
  `placeValue F v (representationEntry F ρ i j)`, that is, `D_X` of the entry function. The
  matrix of `ρ` at a kernel point is `1 + ε · (tangent matrix)` (`Lie.affineMatrix_lieKernel_eq`),
  so the `(i, j)` entry of the right side is the `ε`-part of the value of the entry function at
  `tangentPoint X`. By `affinePointEvaluation_tangentPoint_snd` this `ε`-part is again `D_X` of
  the entry function.
- `tangentKernel_lie`: for identity tangent vectors `X` and `Y`,

  ```text
  tangentKernel ⁅X, Y⁆ = ⁅tangentKernel X, tangentKernel Y⁆
  ```

  in `Additive (lieKernel G F_∞)`. Proof: `G` is smooth over `F`, hence locally of finite type.
  The Library's `affineLinearEmbeddingStatement` gives a matrix representation `ρ` that is a
  closed subgroup embedding, so its underlying morphism is a monomorphism, and
  `Lie.kernelDifferential_injective` makes `ρ.kernelDifferential F_∞` injective. That map takes
  the Library bracket to the matrix commutator (`MatrixRepresentation.kernelDifferential_commutator`).
  By `matrixDifferential_realization` it agrees on `tangentKernel` with `matrixDifferential` of
  the realization, and that map takes Mathlib's bracket to the matrix commutator
  (`MatrixCoefficientLie.matrixDifferential_lie`, which uses the smoothness of the entries).
  Both sides of the claim therefore have the same image under the injective map.

## Provenance

Internal: the identification of the Lie algebra of the real Lie group `G(F_∞)` with the
algebraic Lie algebra `Lie(G) ⊗_F F_∞` respects brackets. The proof is the usual one through a
faithful linear representation, which reduces both brackets to matrix commutators. Together
with `tangentKernel_bijective` (module `InfiniteAdelicTangentKernelBijective`), `tangentKernel_add`
and `tangentKernel_smul`, this says that `X ↦ tangentKernel X` is a bijection compatible with
addition, with real scalars (acting on the kernel through `realAdele` and `lieKernelScale`) and
with brackets. The Library files do not bundle it as a Lie algebra equivalence.
