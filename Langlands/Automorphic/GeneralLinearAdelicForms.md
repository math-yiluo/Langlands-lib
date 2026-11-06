# Original-function general-linear form inclusions

This internal construction compares the existing actual group-scheme and matrix
function spaces for any number field `F` and any natural number `n`. Its
underlying map is the existing `finitePlotSmoothGeneralLinearEquiv`, induced by
the actual adelic-point homeomorphism. Both ambient carriers consist of the
original rational-invariant functions with smooth infinite slices and one common
open finite stabilizer.

`generalLinearStandardInfiniteCompact` is the preimage of the existing matrix
standard infinite compact subgroup under the actual infinite-point
homeomorphism. Its maximal-compact proof transports the existing compactness
and maximality proofs. For any subgroup `U` of the matrix infinite adelic group,
`generalLinearAdelicInfiniteIntertwiner` uses the original continuous-function
comparison and intertwines the subgroup actions. The injective-intertwiner
finite-vector theorem transfers finite orbit spans, and the surjective subgroup
map reindexes the full matrix orbit. Thus
`isAdelicInfiniteFinite_iff_generalLinear` compares finiteness of the whole
function's subgroup orbit, with one finite-dimensional span for all finite
slices simultaneously.

Fix an arbitrary algebraic matrix representation of the actual general-linear
group scheme into `GL_N`, a proof that it is a closed subgroup embedding, and
`0 < N`. Also fix a proof of smooth relative dimension `d`, which specifies the
existing smooth atlas. The theorem
`hasPolynomialGrowth_generalLinear_of_adelicModerateGrowth` first converts the
full adelic moderate bound to a natural-exponent full bound, then restricts that
bound to each finite slice using `GroupSchemeAdelicSliceGrowth`. The existing
closed-embedding independence theorem identifies the resulting slice condition
with the original matrix `HasPolynomialGrowth`.

For every function `f` in the existing finite plot-smooth carrier,
`isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth` proves the exact
equivalence

```
actual adelic form condition on f
  ↔ original matrix form condition on the unchanged image of f
      ∧ full adelic moderate growth of f for the chosen representation.
```

Finite level on the matrix side follows from the common finite stabilizer.
The subgroup-orbit comparison supplies compact finiteness, and
`GeneralLinearAdelicCenterFinite` supplies whole-function center finiteness.
The growth implication above supplies the matrix growth condition. Conversely,
the matrix compact and center conditions transfer back, and the displayed
full adelic growth conjunct supplies the remaining actual form condition.

The retained `hcalc` parameter is a proof of the Prop-valued scalar-commutator
identity on the same atlas. The actual manifold-calculus theorem supplies it in
`isActualAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth`; proof
irrelevance makes the choice of its proof immaterial.

With the existing connected-reductivity premise supplied for the actual
general-linear group scheme, `adelicAutomorphicGeneralLinearMap` restricts the
original function equivalence to an injective complex linear map from
`AdelicAutomorphicForms` to the original `AutomorphicForms F n`. The source
uses the specified transported standard maximal compact and the chosen closed
matrix embedding. Its geometric proof parameters remain explicit.
The value and continuous-inclusion identities show that the map keeps the
original function. `evaluate_adelicAutomorphicGeneralLinearMap` identifies its
values at adelic points corresponding under the original homeomorphism.
The finite-right-action theorem and bundled intertwiner preserve the existing
positive convention `R(c)f(x) = f(x*c)`, with the finite group reindexed by its
actual homeomorphism.

The matrix form definition imposes polynomial growth separately on each finite
slice, whereas the source requires one bound over all adelic arguments. The
extra full-growth conjunct in the equivalence is therefore retained. This unit
constructs an injection and does not establish its surjectivity. It also makes
no assertion of automatic uniform differential growth, a comparison of
cuspidal form spaces, or global finite tensor rank. The separate literal tensor
condition remains an additional condition on the broader finite-smooth
carrier.
