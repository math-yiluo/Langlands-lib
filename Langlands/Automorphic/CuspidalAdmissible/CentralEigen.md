# A central law from an eigenvector of the central archimedean derivative

Provenance: internal. This module supplies the central character input of Harish-Chandra's
finiteness theorem for cusp forms (Harish-Chandra, *Automorphic forms on semisimple Lie
groups*, Lecture Notes in Math. 62, Ch. I). It treats only the real one-parameter group
`t ↦ e^t · 1`, the same scalar at every infinite place. The derivative of this group is the
identity matrix in the real Lie algebra. The identity matrix commutes with every matrix, so
its enveloping generator is central. Every vector of a realization is annihilated by an ideal
of finite codimension in the enveloping center. So the realization contains an eigenvector of
this central derivative. For an eigenvector, a first-order ODE along the central torus gives
the central law used in `Finiteness`. The full center of `GL_n(𝔸)` is not needed here.

Notation: `S : OperatorRealization F n`, `D := ArchimedeanGL.centralGenerator F n`,
`ev f := evaluate F n (S.toContinuous f)` and `centralTorus F n t` (from `Finiteness`), the
adelic matrix with archimedean component `e^t · 1` and finite component `1`.

## The central direction (`Langlands.Global.ArchimedeanGL`)

- `unitDirection K n`: the identity matrix as an element of `RealLieAlgebra K n`.
  `realLieAlgebraToMatrix_unitDirection` says that its matrix is `1`.
- `unitDirection_lie`: `⁅1, X⁆ = 1 · X - X · 1 = 0` for every real direction `X`.
- `complexify_unitDirection_lie`: `⁅1 ⊗ 1, X⁆ = 0` in the complexification. The proof is
  induction on tensors (`TensorProduct.inductionOn`) with `complexLieAlgebra_lie_tmul`.
- `centralGenerator K n`: the enveloping generator of `complexify (unitDirection)`.
- `centralGenerator_mem_center`: `D` lies in the center of the enveloping algebra. Every
  generator `envelopingGenerator X` commutes with `D` by `envelopingGenerator_lie` and the
  previous lemma. The generators span the enveloping algebra as an algebra
  (`LieCasimir.enveloping_adjoin_range`), so the centralizer of `D` is everything.
- `centralElement K n`: `D` as an element of `EnvelopingCenter K n`.

## The ODE and the central law (`Langlands.Automorphic.OperatorRealization`)

- `eq_exp_mul_of_hasDerivAt`: if `h : ℝ → ℂ` satisfies `h'(t) = λ h(t)` for all `t`, then
  `h t = e^{λ t} h 0`. The derivative of `e^{-λ t} h(t)` is zero, so this function is
  constant (`is_const_of_deriv_eq_zero`).
- `ringEquiv_mixedSpace_infiniteRealEmbedding`: in mixed coordinates the real scalar `r`
  becomes `r • 1`.
- `archimedeanGLCoordinates_mul_torInf F n a t`: in mixed matrix coordinates, right
  multiplication by `torInf F n (fun _ => t)` is multiplication by the real scalar `e^t`.
- `smooth_mul_torInf_of_differential s λ hs a t`: let `s` be a smooth function on the
  archimedean group with `smoothDifferential (unitDirection) s = λ • s`. Then
  `s(a · e^t) = e^{λ t} s(a)`.

  Proof: put `A` for the coordinates of `a` and `E` for `coordinateExtension s`. Then
  `s(a · e^t) = E(e^t A)`. The curve `t ↦ e^t A` has derivative `e^t A`, and `E` is
  differentiable at invertible matrices (`coordinateExtension_contDiffAt`). The chain rule
  gives the derivative `fderiv E (e^t A) (e^t A)`. This is the directional derivative
  `smoothDifferential_apply` at `a · e^t` in direction `1`, so it equals `λ s(a · e^t)`.
  Apply `eq_exp_mul_of_hasDerivAt` and `torInf_zero`. The theorem uses
  `open scoped Classical`, which supplies the finiteness instance behind the norm on the
  mixed space.
- `finiteSmoothSlice_centralGenerator`: the archimedean slice at `y` of `D f` is
  `smoothDifferential (unitDirection)` applied to the slice of `f`
  (`finiteSmoothSlice_envelopingAction`, `envelopingAction_real_generator`).
- `evaluate_mul_centralTorus λ f hf g t`: if `D f = λ f`, then
  `ev f (g · centralTorus t) = e^{λ t} ev f g` for every adelic `g`.

  Proof: write `g = g_∞ g_f` (`AdelicGL.eq_ofInfinite_mul_ofFinite`). The slice of `f` at
  `g_f` is an eigenfunction of the central direction. Apply the previous theorem at `g_∞`,
  and move the archimedean factor past `g_f` (`AdelicGL.ofInfinite_commute`).

## The eigenspace and an eigenvector

- `finiteRepresentation_centralEigen`: finite translations preserve the equation
  `D f = λ f`, because they commute with the enveloping action
  (`finiteRepresentation_envelopingAction`).
- `centralEigenspace S λ`: the `λ`-eigenspace of `D`, as a subrepresentation of the finite
  action. `mem_centralEigenspace` unfolds membership to `D f = λ f`.
- `sliceFamilyMap`: the linear map sending `f` to its family of archimedean slices
  `b ↦ finiteSmoothSlice b f`. `sliceFamilyMap_eq` identifies it with `smoothSliceFamily`.
  `sliceFamilyMap_injective` follows from `smoothSliceFamily_injective`.
  `sliceFamilyMap_envelopingAction`: for `z` in the enveloping center, the slices of `z f`
  are `centerFamilyOrbitMap (slices of f) z`.
- `CuspidalAdmissible.exists_eigenvector_of_invariant T W hW hT`: a nonzero
  finite-dimensional complex subspace `W` with `T W ⊆ W` contains an eigenvector of `T`
  (`Module.End.exists_eigenvalue` for the restriction).
- `centerOrbitMap f`: the linear map `z ↦ z f` on the enveloping center
  (`centerOrbitMap_apply`).
- `finite_range_centerOrbitMap f`: the range of `centerOrbitMap f` is finite-dimensional.
  Composed with the injective `sliceFamilyMap`, this map is `centerFamilyOrbitMap` of the
  slice family of `f`. That family is center-finite because `f` is an automorphic form
  (`isAutomorphicForm_ambient`, `IsCenterFinite`).
- `self_mem_range_centerOrbitMap`: `f = 1 · f` lies in the range.
  `centralGenerator_mem_range_centerOrbitMap`: `D (z f) = (D z) f` stays in the range,
  because `D z` is again central.
- `exists_centralEigenvector`: if `S.Space` is nontrivial, there are `λ` and `f ≠ 0` with
  `D f = λ f`. Apply `exists_eigenvector_of_invariant` to `T := D` and the range of
  `centerOrbitMap f₀` for some `f₀ ≠ 0`.

The declarations `centralGenerator_mem_range_centerOrbitMap` and `exists_centralEigenvector`
use `set_option maxHeartbeats 1000000`. Their elaboration goes through the generic
`Submodule` instances of `S.Space`, which is costly.
