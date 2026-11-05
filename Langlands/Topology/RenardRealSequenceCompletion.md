# Real product sequences and their canonical completion maps

This internal construction fixes the scalar field to `ℝ` and the index set to
`ℕ`. Every carrier is in `Type 0`. It supplies concrete objects for a later
investigation of the usual completion with the morphisms printed in Renard;
it asserts no density, properness, convergence or nonextension result.

## Provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
Appendix A.III.1, printed p.251 / one-based PDF257, defines the right universal
problem. Example 2 on printed p.252 / PDF258 describes topological vector spaces,
the full subcategory of complete topological vector spaces, and continuous maps
as morphisms. These pages were read directly and PDF258 was rendered and viewed.
The real sequences, finite truncations, chosen metric and reciprocal function
below are internal constructions motivated by that passage; they do not occur
there as definitions. Fixing `ℝ` gives an ordinary complete separated scalar
field and a real-valued distance and reciprocal, without any carrier-universe
transport. This unit makes no assertion that the printed universal problem is
solved, fails, or has no possible reflection.

## The actual spaces and structures

All declarations are in `Langlands.Renard.RealSequenceCompletion`.
`ProductSequence` abbreviates `ℕ → ℝ`. Its additive group and real module are
Mathlib's pointwise function structures; its topology is the product topology
and its uniformity is `Pi.uniformSpace` applied to the usual real uniformity.
`finiteSequenceSubmodule` is exactly the range of
`Finsupp.lcoeFun (R := ℝ) : (ℕ →₀ ℝ) →ₗ[ℝ] ProductSequence`.
`FiniteSequence` is the carrier subtype of that submodule. The theorem
`mem_finiteSequenceSubmodule` characterizes membership by finiteness of
`Function.support`. The forward proof uses the actual Finsupp support;
the reverse constructs `Finsupp.ofSupportFinite p hp`.

The topology and uniformity on `FiniteSequence` are the inherited subtype
structures. `finiteSequence_topologicalSpace` and `finiteSequence_uniformSpace`
identify them explicitly with the topology and uniformity induced by subtype
inclusion. This is the subspace topology from the product, not a direct-sum
topology. The named `productSequence_*` and `finiteSequence_*` intrinsic laws
expose Mathlib's topological additive group, jointly continuous real scalar
action (`ContinuousSMul`), compatible additive uniformity (`IsUniformAddGroup`)
and uniformly continuous fixed-scalar actions (`UniformContinuousConstSMul`).
The topological additive group and joint scalar-continuity laws are supplied
by the coordinate/product and inherited submodule instances. The product
additive uniform-group law is also an existing instance. The exported instance
`finiteSequence_isUniformAddGroup` pulls back that law along the actual linear
subtype map using `IsUniformAddGroup.comap`. The two exported fixed-scalar
uniform-continuity instances use
`uniformContinuousConstSMul_of_continuousConstSMul`, deriving uniform continuity
from the continuous additive scalar maps on these additive uniform groups.
The product is complete by the product completeness instance, and Hausdorff by
the product separation instance; the corresponding named laws are
`productSequence_completeSpace` and `productSequence_t2Space`.

`inclusion` is the actual `finiteSequenceSubmodule.subtypeL`. Its value and
coordinate laws are definitional. Injectivity is `Subtype.val_injective`,
and `inclusion_isUniformEmbedding` is Mathlib's uniform embedding of a subtype.

## Explicit sequences and distance

`missingSequence` is the constant-one sequence, with its coordinate law.
The name designates its intended later use and carries no proved nonmembership
assertion. `truncateFinsupp n p` is built using `Finsupp.onFinset` on
`Finset.range n` and the function `i ↦ if i < n then p i else 0`. Its explicit
support proof gives zero outside that finite set; the exported support law is
`truncateFinsupp_support_subset`. `truncate n p` is the image of that actual
Finsupp, paired with this range witness. `inclusion_truncate` proves its exact
coordinate formula and `truncate_zero` proves the zero truncation.

`sequenceMetricSpace` is the explicit `PiCountable.metricSpace`, with real
coordinate metrics and the standard `Encodable ℕ` instance. It is not installed
as a global instance. `sequenceDistance` invokes its distance explicitly.
The definitional law `sequenceDistance_eq_tsum` is

```text
sequenceDistance p q =
  ∑' i, min ((2⁻¹ : ℝ) ^ Encodable.encode i) (dist (p i) (q i)).
```

`sequenceMetricSpace_uniformSpace` identifies its uniform structure with the
original product uniformity, and `sequenceMetricSpace_topologicalSpace` does
the same for the topology. Both are definitional equalities: Mathlib's
`PiCountable.pseudoEMetricSpace` retains `Pi.uniformSpace`, and its subsequent
metric constructors retain that uniformity and its topology. No metric
instance replaces the inherited uniformity or topology of either space.

`reciprocalDistance x` is exactly
`(sequenceDistance (inclusion x) missingSequence)⁻¹`, as recorded by
`reciprocalDistance_apply`. The inverse is the total real inverse. Neither a
nonzero-denominator assumption nor a conclusion about it occurs here.

## Actual uniform completion

`SequenceCompletion` abbreviates `UniformSpace.Completion FiniteSequence`
for the inherited uniformity. Its operations are Mathlib's existing completion
additive group and `UniformSpace.Completion.instModule` over `ℝ`; the required
fixed-scalar uniform continuity is supplied above. This does not assert joint
scalar continuity on the completion.

`toCompletion` is `UniformSpace.Completion.toComplL`. Its underlying-function
and pointwise laws identify it with the actual coercion into the completion.
`completionToProduct` is `ContinuousLinearMap.fromCompletion inclusion`, using
the complete separated product as target. `coe_completionToProduct` identifies
its underlying function with `UniformSpace.Completion.extension inclusion`.
`completionToProduct_coe` is Mathlib's `fromCompletion_apply_coe` agreement law,
and `completionToProduct_toCompletion` states the same agreement using the named
canonical map.

The construction assumes no dense inclusion, alternative complete model,
completion equivalence, inverse, or nonextension certificate. Density,
properness, convergence of truncations, reciprocal continuity, comparison with
the product, joint scalar continuity on the completion and failure of continuous
extension remain separate statement/proof or general-completion obligations.

## Mathlib implementation sources

At pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, the
implementation uses `Mathlib.LinearAlgebra.Finsupp.Pi`,
`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict`,
`Mathlib.Topology.MetricSpace.PiNat` (the nondiscrete-coordinate `PiCountable`
construction), and `Mathlib.Topology.Algebra.LinearMapCompletion`. Intrinsic
proofs use the subtype constructions, actual finite-support witnesses and
Mathlib completion agreement lemmas just described.
