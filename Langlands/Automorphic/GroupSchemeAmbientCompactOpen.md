# Compact-open topology on the original group-scheme ambient functions

The declarations are in
`Langlands.Automorphic.GroupSchemeFunctions.CompactOpen`.
They apply to an arbitrary-universe number field `F` and actual affine group
schemes over `Spec F`. Connectedness and reductivity are not needed for these
ambient function constructions.

`toContinuousMap` is the complex linear faithful realization of the existing
`ContinuousRationalFunctions F G` as continuous complex-valued functions on
`AdelicGroupPoints F G`: its value at `x` is exactly `f.val.val x`.
`toContinuousMap_injective` proves faithfulness.

`instTopologicalSpace` selects the topology induced from the compact-open
topology on `C(AdelicGroupPoints F G, ℂ)`. This is an opt-in scoped instance:

```lean
open scoped Langlands.Automorphic.GroupSchemeFunctions.CompactOpen
```

The carrier, complex vector-space operations and original positive right action
are unchanged. Importing this module does not globally replace the topology
inherited from the function subtypes. `isEmbedding_toContinuousMap` states the
embedding for the selected topology. Scoped instances
`instIsTopologicalAddGroup`, `instContinuousSMul` and `instT2Space` prove that
addition, negation and joint complex scalar multiplication are continuous and
that the selected topology is Hausdorff.

`toContinuousMapCLM` bundles the same faithful realization as a continuous
linear map. `evalCLM F G x` is continuous complex linear evaluation at an actual
adelic point; `evalCLM_apply` gives its unchanged value.
`continuous_rightAction` proves compact-open continuity of every fixed original
positive right translation. `rightTranslationCLM` bundles that same operator,
and its value law is exactly `R(g)f(x) = f(x * g)`.

For an actual group-scheme morphism `φ : G ⟶ H`, `continuous_pullback` proves
continuity of the existing `continuousPullback F φ`. `pullbackCLM` bundles this
same linear map, with an explicit `toLinearMap` equality and unchanged value
formula. Its identity law and contravariant composition law are equalities of
continuous linear maps. `pullbackCLM_rightAction` retains the original positive
action law, restricting the target action along the actual adelic point map of
`φ`. For an actual group-scheme isomorphism `e : G ≅ H`,
`pullbackContinuousLinearEquiv` bundles the existing `continuousPullbackEquiv`;
the underlying linear equivalence and both directions of pointwise evaluation
are recorded explicitly.

In every natural matrix rank, including zero, `continuous_generalLinearEquiv`
and `continuous_generalLinearEquiv_symm` prove continuity of both directions of
the original matrix comparison. `generalLinearContinuousLinearEquiv` is the
resulting continuous complex linear equivalence to the original
`Langlands.Automorphic.ContinuousRationalFunctions F n`, with its existing
compact-open topology from `Ambient`. Its underlying linear equivalence is
exactly `continuousGeneralLinearEquiv`. The forward value is composition with
the inverse of `GeneralLinearGroupPoints.adelicHomeomorph F n`; the inverse
value is composition with that homeomorphism. The full positive right action
is intertwined by `generalLinearContinuousLinearEquiv_rightAction`.

This is internal implementation content derived from the published
`GroupSchemeAmbient`, `GroupSchemeAmbientFunctorial` and `Ambient` constructions.
The embedding follows from induced topology and injectivity. Transport along
the faithful linear realization gives the topological vector-space properties.
Continuous precomposition gives fixed translation, morphism pullback and both
comparison continuities; the functorial and action laws reuse the original
algebraic maps. No external-source theorem is asserted here. This unit makes
no claim about the compact-open topology of quotient functions, joint group
action continuity, automorphic regularity, growth, finite volume or Hilbert
identification.
