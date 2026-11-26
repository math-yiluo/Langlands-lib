# Transposes of enveloping operators on the infinite adelic points

Module `Langlands.Global.InfiniteAdelicIntegrationByParts` applies
`Langlands.Geometry.Manifold.LieGroupIntegrationByParts` to `G(F_∞) = InfiniteAdelicGroupPoints F G`
with the Lie group structure of a smooth structure `hsmooth` (`smoothChartedSpace`,
`smoothLieGroup`).

## Declarations

- `compactPlotSmoothFunctions F G`: the submodule of `InfinitePlotSmoothFunctions F G` of
  functions with compact support.
- `continuous_of_mem_infinitePlotSmoothFunctions`: plot-smooth functions are continuous, by
  `isPlotSmooth_iff_contMDiff`.
- `integrable_mul_compactPlotSmooth`: for a measure finite on compact sets, the product of a
  plot-smooth function and a compactly supported plot-smooth function is integrable.
- `exists_envelopingAction_transpose`: for a right-invariant measure `ν` finite on compact sets and
  every `y` in the complex enveloping algebra `AdelicEnvelopingAlgebra F G hsmooth`, there is a map
  `T` on compactly supported plot-smooth functions with
  `∫ (y f) ψ dν = ∫ f (T ψ) dν` for all plot-smooth `f` and compactly supported `ψ`, where `y`
  acts by `plotSmoothEnvelopingAction`.
- `eq_zero_of_forall_integral_compactPlotSmooth`: for a measure positive on nonempty open sets and
  finite on compact sets, a continuous function whose integrals against all compactly supported
  plot-smooth functions vanish is zero.

## Proof of the transpose

The set of `y` that have a transpose contains `1` (with `T = id`). It is closed under sums
(`T_a + T_b`, using the integrability lemma), complex scalar multiples (`c T_a`) and products
(`T_{a b} = T_b ∘ T_a`, since the action is multiplicative). A real generator `ι(1 ⊗ X)` acts by
`plotSmoothDifferential X`, that is by `groupDirectionalValue X`
(`plotSmoothEnvelopingAction_real_generator`). Its transpose is `ψ ↦ -X ψ`, which preserves compact
support, by `integral_groupDirectionalValue_mul`. A complex generator `ι(c ⊗ X)` is
`c • ι(1 ⊗ X)`, and induction over the tensor product covers `ι` of every element. Every element
of the enveloping algebra is the image of an element of the tensor algebra, so induction over the
tensor algebra (`TensorAlgebra.induction`) finishes the proof.

Separation is `eq_zero_of_forall_integral_mul_eq_zero` for this Lie group, with the smooth test
functions translated into compactly supported plot-smooth functions by `isPlotSmooth_iff_contMDiff`.

## Provenance

Internal analytic tools. They let the uniform center ideal of intertwining integrals be checked
weakly, against test functions, without differentiating under a noncompact integral.
