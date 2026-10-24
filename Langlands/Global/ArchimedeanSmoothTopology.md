# The actual archimedean derivative compact-open topology

This module constructs the topology of uniform convergence on compact sets of
all genuine enveloping derivatives. It applies to every `K : Type u` with
`[Field K] [NumberField K]` and every natural rank `n`, including zero. It
imports the published `ArchimedeanEnvelopingAction` and Mathlib's
`Topology.ContinuousMap.LocallyConvex`. It changes no existing declaration or
instance on `SmoothFunctions K n`.

## Carrier and coordinates

In `Langlands.Global.ArchimedeanGL`, `DerivativeSmoothFunctions K n` is a
dedicated type synonym for the actual published `SmoothFunctions K n`. Its
algebraic instances are inherited. In its namespace, `toSmooth` is the
canonical complex linear equivalence with that published carrier. This is
an algebraic equivalence; no homeomorphism to the carrier's inherited
pointwise topology is asserted.

Write `G = Matrix.GeneralLinearGroup (Fin n)
(NumberField.InfiniteAdeleRing K)`, the actual group also called
`InfiniteAdelicGL K n`, and `D(a) = envelopingAction K n a`.
`derivativeCoordinates` is the complex linear map

```
f ↦ (a ↦ toContinuousMap K n (D(a) (toSmooth K n f)))
```

into the product over `a : EnvelopingAlgebra K n` of `C(G, ℂ)`. Every factor
has Mathlib's compact-open topology. The topology on the new carrier is
explicitly `TopologicalSpace.induced derivativeCoordinates inferInstance`.
The coordinates are the existing actual differential operators, not a
parameterized replacement action or supplied continuity hypothesis.

`derivativeCoordinates_one` identifies the unit coordinate with the original
continuous function. Together with the published `toContinuousMap_injective`
and the equivalence `toSmooth`, it proves `derivativeCoordinates_injective`.
Thus `isEmbedding_derivativeCoordinates` is a topological embedding into the
product of compact-open continuous-function spaces.

## Topological vector space and differential maps

The embedding induces `IsTopologicalAddGroup`, `ContinuousSMul ℂ`,
`ContinuousSMul ℝ`, and `T2Space` instances. The complex and real module
structures satisfy `IsScalarTower ℝ ℂ`. The instance
`LocallyConvexSpace ℝ (DerivativeSmoothFunctions K n)` is pulled back from
the product of continuous-function spaces through the real restriction of
the coordinate linear map. In Mathlib convexity uses ordered scalars, so
real local convexity together with continuous complex scalar multiplication
expresses the locally convex complex topological vector space requested here.

`derivativeCLM K n a` is the continuous complex linear map to `C(G, ℂ)`
selecting coordinate `a`; `derivativeCLM_apply` gives its exact actual
derivative formula. `operator K n a` transports the published `D(a)` through
`toSmooth` and its inverse. Its transport formula is `toSmooth_operator`.
The theorem `derivativeCoordinates_operator` states

```
derivativeCoordinates (operator a f) b = derivativeCoordinates f (b * a).
```

This follows directly from the published multiplication law
`D(b*a)f = D(b)(D(a)f)`. Each coordinate of `operator a` is therefore a
continuous coordinate map. The induced topology and product continuity
criterion prove `continuous_operator`. `operatorCLM K n a` bundles the
result; its continuity is proved, not assumed.

`toContinuousMapCLM` is the unit-coordinate continuous linear map to actual
continuous functions. Its application theorem identifies it with the
published `toContinuousMap` after `toSmooth`, and
`toContinuousMapCLM_injective` proves faithfulness. Composing with Mathlib's
continuous evaluation gives `evalCLM K n x`. The theorem `evalCLM_apply`
identifies its value with `(toSmooth K n f).val x`.

## Convergence and neighborhoods

For any index type, any filter `l`, a family `F` and a proposed limit `f`,
`tendsto_iff_derivativeCoordinates` says that `F` converges to `f` precisely
when each derivative coordinate converges in `C(G, ℂ)`.
`tendsto_iff_uniformOn_compact` identifies this with uniform convergence on
every compact subset of `G` of every derivative. This uses Mathlib's
`ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn`; there is no
restriction to sequences or any extra local compactness hypothesis.

`nhds_eq_iInf` identifies the neighborhood filter of `f` with the infimum,
over all enveloping elements `a`, of the pullbacks of the compact-open
neighborhood filters at `derivativeCoordinates f a`. The proof uses the
inducing map's neighborhood formula, the product neighborhood formula, and
commutation of filter pullback with infima. Thus the topology has its intended
meaning for arbitrary filters and closures, not only pointwise evaluation.

## Source and implementation provenance

Harish-Chandra, *Discrete series for semisimple Lie groups II: Explicit
determination of the characters* (1966), §5, printed page 12, describes the
smooth-function topology by the seminorms `sup_{x ∈ Ω} |D(a)f(x)|`, for compact
`Ω` and enveloping elements `a`. In the retained PDF this is one-based PDF
page **11**: printed pages 11 and 12 occur in reverse order. The displayed
seminorm and its surrounding text were checked in the rendered original.
Registered source: `harish-chandra-1966-discrete-series-ii`; SHA256
`3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`.
The retained file is
`literature/Harish-Chandra, Discrete series for semisimple Lie groups II- Explicit determination of the characters (1966).pdf`.
Sections 2, 5, and 7–8, printed pages 5–7, 12–19, were also read for the
representation setting and scope. No source-specific errata file was found
in the available project literature or Library notes.

This is a derived implementation of that derivative compact-convergence
topology on the project's already constructed actual archimedean smooth
functions. It uses an induced product topology rather than separately
bundling supremum seminorms. The coordinate injectivity, transferred
structures, differential continuity, and filter formulas are implementation
proofs using the published action laws and the pinned Mathlib infrastructure
(commit `5ed2965256430c3649e86755f9576b54eca72435`). No analytic theorem from
the source is assumed as an axiom.

## Remaining obligations

The module does not prove completeness, metrizability, or equality with a
separately defined coordinate Fréchet topology. It does not construct joint
continuity or smoothness of the full group action, integration in locally
convex spaces, analytic regularity, finite-dimensional compact-type
projections, smooth approximate identities, or reproducing kernels. Those
are separate obligations. In particular, Harish-Chandra's Theorem 1 in §8
uses the connected reductive setting and hypotheses of §7; this construction
does not establish that theorem for the full completion-based, possibly
disconnected general linear group.
