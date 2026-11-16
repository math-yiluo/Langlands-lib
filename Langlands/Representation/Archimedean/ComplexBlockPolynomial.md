# Functions polynomial along a root subgroup

## Definitions

- `bidegLT p q`: the span of the functions `z ↦ z^a z̄^b` on `ℂ` with `a < p`, `b < q`
  (finite-dimensional, `bidegLT_finiteDimensional`).
- `rootMatrix i j z = 1 + z E_{j,i}` and, for `i ≠ j`, the unit `rootUnit hij z`
  (inverse `rootUnit hij (-z)`, `rootMatrix_mul_neg`).
- `IsBlockPoly hij p q F`: for every `g ∈ GL_n(ℂ)`, `z ↦ F (rootUnit hij z · g)` lies in
  `bidegLT p q`; `blockPolySubmodule hij p q` is the subspace of such `F`.

## Results

- `bidegLT_mono`, `const_mem_bidegLT`; `affine_mul_mem`, `conj_affine_mul_mem`: multiplying by an
  affine function `c₀ + c₁ z` (or its conjugate) raises the bound `p` (or `q`) by one.
- `isBlockPoly_rightTranslation`: right translates of block-polynomial functions are
  block-polynomial (left and right multiplication commute).
- `isBlockPoly_rightDerivative`: for a smooth `F` (`ContMDiff` on `GL_n(ℂ)`), the right
  derivative `rightDerivative X F` is block-polynomial if `F` is. For fixed `g`, with
  `Φ = unitsExtension F` (zero off the units), the functions
  `z ↦ Φ(rootMatrix z · (g + t g X))` (`t ∈ ℝ`) lie in `bidegLT p q`: when `g + t g X` is a unit
  this is block polynomiality at that unit, otherwise the function is `0`. Their
  `t`-derivative at `0` is `z ↦ (R(X) F)(rootUnit z · g)`, which therefore lies in
  `bidegLT p q` by `FiniteFunctionSpaces.mem_of_hasDerivAt`.

## Provenance

Internal infrastructure of Task 7064 for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
