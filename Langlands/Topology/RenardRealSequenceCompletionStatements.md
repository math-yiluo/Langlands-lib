# Concrete real-sequence completion and continuous nonextension statements

This module defines eleven closed propositions and their closed conjunction.
Every conclusion remains an exact proof obligation. Defining these propositions
does not establish a counterexample, a source correction, or a failure of every
possible reflection into complete spaces.

## Provenance and scope

The motivating original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Appendix A.III.1, printed p.251 / one-based PDF257, defines the right universal
problem by unique factorization. Example 2, printed p.252 / PDF258, describes
topological vector spaces, their full subcategory of complete topological
vector spaces, and continuous maps as morphisms. It names the completion and
canonical continuous inclusion as a solution. The passage imposes no linearity
condition on morphisms and specifies no fixed scalar field. Both pages were
read directly, and rendered PDF258 was viewed for the morphism convention.

The supplementary registered source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is the author's correction list for the older 2010 edition. Its PDF18–19
contain no correction of this example. This is a bounded check of those pages,
not a claim about all possible errata or about a corrected 2026 convention.

The real sequences, chosen finite subspace, metric, reciprocal and the
propositions below are internal mathematical tests motivated by that convention;
they are not literal assertions of Renard. They fix the field to `ℝ`, a complete
separated topological field, and fix the target to `ℝ`, already a complete
separated real topological vector space. The intended test concerns the actual
usual uniform-completion arrow under the literal all-continuous-maps convention.
The separate continuous-linear and uniformly continuous completion problems
retain their own scope. This statement module proves none of these problems
or the proposed obstruction.

## Actual objects and unchanged structures

The module imports `Langlands.Topology.RenardRealSequenceCompletion` for the
actual objects and `Mathlib.Topology.Algebra.Module.Equiv` for real continuous
linear equivalences. Every declaration below belongs to
`Langlands.Renard.RealSequenceCompletion`, and every carrier is in `Type 0`.
There are no space parameters, certificates or outer hypotheses.

`ProductSequence` is exactly `ℕ → ℝ` with Mathlib's pointwise real module,
product topology and `Pi.uniformSpace` from the usual real uniformity.
`finiteSequenceSubmodule` is the actual range of
`Finsupp.lcoeFun (R := ℝ) : (ℕ →₀ ℝ) →ₗ[ℝ] ProductSequence`.
`FiniteSequence` is its carrier subtype, with the topology and uniformity
inherited from the product. The prerequisite's
`finiteSequence_topologicalSpace` and `finiteSequence_uniformSpace` identify
these with the structures induced by `Subtype.val`. No direct-sum topology is
introduced. `inclusion` is the published continuous real-linear subtype map.
`missingSequence` is the constant-one sequence.
`truncate n p` is the published finite-support element whose image has
coordinate `if i < n then p i else 0`.

`sequenceMetricSpace` is the explicit `PiCountable.metricSpace`; it is not
installed as a global instance here or in the prerequisite.
`sequenceDistance` uses its distance explicitly, with formula

```text
sequenceDistance p q =
  ∑' i, min ((2⁻¹ : ℝ) ^ Encodable.encode i) (dist (p i) (q i)).
```

The prerequisite's `sequenceMetricSpace_uniformSpace` and
`sequenceMetricSpace_topologicalSpace` show definitionally that this metric
retains the original product uniformity and topology.
`reciprocalDistance x` is the raw total real inverse
`(sequenceDistance (inclusion x) missingSequence)⁻¹`.
Its definition requires no nonzero-denominator hypothesis. Positivity and
continuity are conclusions in this statement family.

`SequenceCompletion` is the actual
`UniformSpace.Completion FiniteSequence` for the inherited uniformity.
It retains Mathlib's completion topology, additive group, and real module
operations. `toCompletion` is the actual
`UniformSpace.Completion.toComplL`, whose underlying function is the
canonical completion coercion. `completionToProduct` is the actual
`ContinuousLinearMap.fromCompletion inclusion`, whose underlying function
is `UniformSpace.Completion.extension inclusion`.
The prerequisite proves `completionToProduct_toCompletion`, the agreement
on original points; it does not construct an equivalence.

The product and finite subspace already have their published topological
additive group and jointly continuous real scalar action structures.
The product is complete and Hausdorff. On the finite subspace the existing
additive uniformity is explicitly the subtype pullback, and the published
`finiteSequence_isUniformAddGroup` supplies compatibility with addition.
For an additive uniform group,
`IsUniformAddGroup.rightUniformSpace_eq` identifies the canonical additive
uniformity with that existing uniformity. Thus the general construction in
`Langlands.Topology.RenardTopModuleCompletion`, in particular
`Langlands.Renard.TopModuleCompletion.completionContinuousSMul`, is a
possible proof resource after this identification. The present declaration
`CompletionJointScalarContinuity` directly concerns Mathlib's existing action
and topology on the actual `SequenceCompletion`. It installs no replacement
structure and takes no joint-continuity certificate as a premise.

## Exact proposition family

The following names are relative to the namespace above.
Each declaration is a `def` returning `Prop`, with no parameters.

| Declaration | Exact assertion |
| --- | --- |
| `TruncationsConverge` | For every `p : ProductSequence`, `Filter.Tendsto (fun n : ℕ => inclusion (truncate n p)) Filter.atTop (nhds p)`, in the existing product topology. |
| `InclusionDenseRange` | `DenseRange (inclusion : FiniteSequence → ProductSequence)`. |
| `MissingSequenceOutsideSubmodule` | `missingSequence ∉ finiteSequenceSubmodule`. |
| `MissingSequenceOutsideInclusion` | `missingSequence ∉ Set.range (inclusion : FiniteSequence → ProductSequence)`. |
| `FiniteSequenceIncomplete` | `¬ CompleteSpace FiniteSequence`, for its existing inherited uniformity. |
| `DistanceToMissingPositive` | For every `x : FiniteSequence`, `0 < sequenceDistance (inclusion x) missingSequence`. |
| `ReciprocalDistanceContinuous` | `Continuous reciprocalDistance`, for the inherited source topology and usual real target topology. |
| `CompletionProductComparison` | There exists `e : SequenceCompletion ≃L[ℝ] ProductSequence` with `(e : SequenceCompletion → ProductSequence) = (completionToProduct : SequenceCompletion → ProductSequence)` and, for every `x : FiniteSequence`, `e (toCompletion x) = inclusion x`. |
| `CompletionJointScalarContinuity` | `ContinuousSMul ℝ SequenceCompletion`, for the existing real action and completion topology. |
| `NoProductContinuousExtension` | The negated existence statement displayed below for functions on `ProductSequence`. |
| `NoCompletionContinuousExtension` | The negated existence statement displayed below for functions on `SequenceCompletion`. |

The complete product nonextension quantifiers are

```text
¬ ∃ g : ProductSequence → ℝ,
    Continuous g ∧
      ∀ x : FiniteSequence, g (inclusion x) = reciprocalDistance x.
```

The complete canonical-completion nonextension quantifiers are

```text
¬ ∃ g : SequenceCompletion → ℝ,
    Continuous g ∧
      ∀ x : FiniteSequence, g (toCompletion x) = reciprocalDistance x.
```

In both declarations `g` ranges over all functions of the stated type.
Continuity is its only map condition: no linearity, additivity, boundedness
or uniform continuity is imposed. The second proposition fixes the published
actual canonical arrow `toCompletion`; it does not quantify over alternative
completion arrows or possible reflections. The comparison proposition fixes
the underlying function of the equivalence to the named actual
`completionToProduct`, rather than merely asserting some homeomorphism.

`CompletionCounterexampleStatements` is the conjunction of all eleven
declarations in the order listed in the table. In particular, density,
missing-point nonmembership, incompleteness, positivity, reciprocal continuity,
the exact completion comparison, joint scalar continuity and both nonextension
claims are conclusions. None is supplied as data to another declaration or
assumed as an outer premise.

## Remaining proof boundary

A future exact proof must prove this aggregate over the unchanged actual
objects, including the comparison equivalence and joint scalar continuity.
The present module contains proposition definitions only and claims no proof
of any component. Statement compilation and eventual statement publication
must not be counted as a source counterexample, source correction, or completion
of the surrounding Renard section.
