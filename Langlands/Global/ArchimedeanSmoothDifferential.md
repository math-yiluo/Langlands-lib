# Genuine smooth archimedean directional differentiation

Author: Worker 84. Namespace: `Langlands.Global.ArchimedeanGL`.

For a number field `K : Type u` and every natural rank `n`, including zero,
this module constructs the real-linear map

```
realSmoothDifferential K n :
  RealLieAlgebra K n →ₗ[ℝ] Module.End ℂ (SmoothFunctions K n).
```

The domain is the published real matrix Lie algebra, and the codomain consists
of actual complex-linear endomorphisms of the published smooth-function space.
For a real direction `X`, `smoothDifferential K n X` is the corresponding
endomorphism. If `g` denotes the mixed-coordinate matrix of a point in the
completion-based group, its evaluation is

\[
(D_X f)(g)=d\widetilde f_g(gX).
\]

Here the differential is the real Fréchet differential and `tilde f` is the
coordinate expression defined below. Complex coefficients remain a real
vector space for differentiation, retaining both real directions at each
complex place. The direction `gX` is the left-invariant matrix vector field
corresponding to the convention `R(h)f(g)=f(gh)` in `smoothRightAction`.
No bracket-preservation or translation-intertwining law is claimed in this
module; those are further analytic obligations.

## Coordinate expression and well-definedness

`unitsChart` is the open partial homeomorphism furnished by the open embedding
of matrix units into matrices. It is the global chart underlying the published
units manifold. Its source is the full group and its target is the open set of
invertible matrices. `coordinateExtension f` composes its total inverse with
`archimedeanGLCoordinates.symm` and the actual function `f`. As with every
partial homeomorphism in Lean, the inverse has values outside its target, but
no assertion about smoothness at those outside points is used.

`coordinateExtension_apply` proves that at every unit the coordinate expression
is exactly the original function in mixed coordinates.
`coordinateExtension_contDiffOn` proves real `C∞` smoothness on the range of the
units embedding. The proof composes the smooth transported function with
Mathlib's smooth inverse of an open embedding and then converts manifold
smoothness between vector spaces to ordinary smoothness.
`coordinateExtension_contDiffAt` uses openness to obtain genuine local `C∞`
regularity at every unit. Thus the Fréchet derivative used in `directionalValue`
is the actual derivative there, rather than relying on the default value of
`fderiv` at a nondifferentiable point.

`smoothDifferential_eq_of_extension` makes the independence from the chosen
total extension precise. For any function `F` from ambient matrices to the
complex numbers satisfying

\[
F(h)=f(\mathrm{coordinates}^{-1}(h))\quad\text{for every unit }h,
\]

the displayed formula for `D_X f` is unchanged if `coordinateExtension f` is
replaced by `F`. No global smoothness hypothesis on `F` is needed. Both
functions agree on the open set of units, so they are eventually equal at
each evaluation point, and Mathlib's `EventuallyEq.fderiv_eq` identifies their
derivatives. In particular arbitrary values away from that open set cannot
affect the construction.

## Smoothness and linearity proofs

`directionalValue_mem` proves that the directional derivative belongs to the
same smooth-function submodule. At each unit, the local `C∞` regularity of the
coordinate expression gives local `C∞` regularity of its Fréchet derivative
via `ContDiffAt.fderiv_right`. Applying that continuous linear map to the
smooth matrix field `h ↦ hX` preserves smoothness. Composition with the smooth
units embedding and the inverse coordinate cancellation gives precisely the
membership predicate of the existing `smoothFunctions` submodule.

`smoothDifferential` packages these values and this closure proof. Additivity
and complex scalar compatibility follow from `fderiv_add` and
`fderiv_const_smul`, using the proved local differentiability at units.
`smoothDifferential_apply` records the exact evaluation formula, with the
completion-to-mixed coordinate map explicit. `realSmoothDifferential` then
packages additivity and real scalar compatibility in `X`, using linearity of
the Fréchet derivative and matrix multiplication. These are intrinsic
well-definedness and linearity proofs for this construction, not assumptions
on a supplied differential action.

## Provenance and scope

This is a derived construction realizing the real archimedean differential
setting of Borel and Jacquet, *Automorphic forms and automorphic
representations*, Corvallis Part I (1979), section 1.1, printed p.189
(one-based PDF p.184), and section 4.1, printed p.194 (PDF p.189). The latter
specifically views the product of archimedean groups as a real Lie group and
uses smooth complex-valued functions. The registered original is
`borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Worker 84 read these original pages. The chart extension, directional formula,
and closure proofs are implementation details derived from that setting,
not assertions quoted verbatim from the source.

The construction imports the accepted `ArchimedeanGL` smooth-function model
through `ArchimedeanLieAlgebra` and reuses the pinned Mathlib real Fréchet
calculus and units manifold. It does not change those published definitions,
introduce an arbitrary action parameter, assume an analytic law, or impose
compact-type or enveloping-center finiteness. Complexification, the Lie
commutator law, and the universal-enveloping-algebra action remain separate
work.
