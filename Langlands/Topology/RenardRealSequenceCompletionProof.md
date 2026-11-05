# Real-sequence completion and continuous nonextension

The theorem
`Langlands.Renard.RealSequenceCompletion.completionCounterexampleStatements`
proves exactly the published closed proposition
`Langlands.Renard.RealSequenceCompletion.CompletionCounterexampleStatements`
from `Langlands.Topology.RenardRealSequenceCompletionStatements`.
The construction and statement modules remain unchanged.

All declarations are in `Langlands.Renard.RealSequenceCompletion`.
There are no outer mathematical premises or universe parameters.
`ProductSequence` is the actual `ℕ → ℝ` with its product topology and
`Pi.uniformSpace`; `FiniteSequence` is the actual range submodule of
`Finsupp.lcoeFun`, with inherited subtype topology and uniformity.
All carriers are in `Type 0`. The proof retains the published truncations,
constant-one missing point, total real reciprocal and canonical maps.
`SequenceCompletion` is the actual `UniformSpace.Completion FiniteSequence`,
`toCompletion` is the actual `UniformSpace.Completion.toComplL`,
and `completionToProduct` is `ContinuousLinearMap.fromCompletion inclusion`.

The eleven constituent theorems have the following exact targets:

| Theorem | Published proposition |
| --- | --- |
| `truncationsConverge` | `TruncationsConverge` |
| `inclusionDenseRange` | `InclusionDenseRange` |
| `missingSequenceOutsideSubmodule` | `MissingSequenceOutsideSubmodule` |
| `missingSequenceOutsideInclusion` | `MissingSequenceOutsideInclusion` |
| `finiteSequenceIncomplete` | `FiniteSequenceIncomplete` |
| `distanceToMissingPositive` | `DistanceToMissingPositive` |
| `reciprocalDistanceContinuous` | `ReciprocalDistanceContinuous` |
| `completionProductComparison` | `CompletionProductComparison` |
| `completionJointScalarContinuity` | `CompletionJointScalarContinuity` |
| `noProductContinuousExtension` | `NoProductContinuousExtension` |
| `noCompletionContinuousExtension` | `NoCompletionContinuousExtension` |

For every `p` and coordinate `i`, the published `truncate n p` agrees with
`p i` once `i + 1 ≤ n`. `tendsto_pi_nhds` turns eventual coordinate equality
into convergence in the original product topology. Every `p` is thus in the
closure of the actual inclusion range, proving density.
`mem_finiteSequenceSubmodule` identifies membership with finite support,
whereas the constant-one sequence has support `Set.univ : Set ℕ`.
This proves both nonmembership assertions. If the inherited finite subspace
were complete, its uniform embedding into the Hausdorff product would have
closed range. Density would then put the missing point in that range,
a contradiction.

The proofs of positivity and metric continuity use a local instance of
the published `sequenceMetricSpace`. Its uniformity and topology are
definitionally the original product structures, so these proofs establish
claims for those original structures. No metric or topology is replaced
globally. Positive distance follows from the missing-point nonmembership.
The helper `sequenceDistance_continuous` proves continuity of
`p ↦ sequenceDistance p missingSequence`. Composition with `inclusion`
and `Continuous.inv₀`, using the proved positivity at every finite sequence,
establish continuity of the published raw total inverse
`reciprocalDistance x = (sequenceDistance (inclusion x) missingSequence)⁻¹`.

For the comparison, a local `AbstractCompletion FiniteSequence` uses
exactly `ProductSequence`, its original uniformity and the actual inclusion.
Its fields follow from the product's completeness and separation, the
published uniform embedding, and the newly proved density.
`AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg pkg`
supplies a uniform equivalence from the actual completion to the product.
Its forward function is definitionally `completionToProduct`.
The proof bundles that named map, its existing additive and scalar laws,
and the uniform comparison's inverse into a real continuous linear
equivalence `e`. The required forward-function equality is `rfl`, and
`completionToProduct_toCompletion` gives agreement on every original point.

Joint scalar continuity follows directly from that equivalence:
the function `(r,z) ↦ e.symm (r • e z)` is continuous for the original
completion topology and equals `(r,z) ↦ r • z` by the existing linear
laws. Thus the conclusion concerns Mathlib's existing completion action,
without introducing another action or assuming joint continuity.

For product nonextension, suppose an arbitrary `g : ProductSequence → ℝ`
is continuous and satisfies `g (inclusion x) = reciprocalDistance x`
for every `x : FiniteSequence`. The continuous function
`p ↦ sequenceDistance p missingSequence * g p` equals one on the dense
inclusion range by `mul_inv_cancel₀` and proved positivity.
`DenseRange.equalizer` makes it identically one. Evaluation at
`missingSequence` gives `0 = 1`, since its distance to itself is zero.
For completion nonextension, any continuous `g : SequenceCompletion → ℝ`
satisfying `g (toCompletion x) = reciprocalDistance x` for every finite
`x` would yield the forbidden product extension `p ↦ g (e.symm p)`.
Neither competitor is required to be linear, additive, bounded or uniformly
continuous. The final theorem conjoins these eleven proved conclusions.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Appendix A.III.1, printed p.251 / one-based PDF257, defines the right
universal problem. Example 2, printed p.252 / PDF258, gives continuous
maps as morphisms between topological vector spaces and selects the full
subcategory of complete spaces. It names the completion and its canonical
continuous inclusion as a solution, without specifying linearity or a fixed
scalar field. Both pages were read for this proof.

The sequence construction, reciprocal and these concrete conclusions are
internal tests motivated by that convention, not literal assertions of
Renard. The proof establishes an obstruction for the actual usual
uniform-completion arrow, already over `ℝ` and with the complete separated
real target `ℝ`. It makes no assertion that every possible reflection into
complete spaces fails to exist, and establishes no broader source correction
or completion of the Renard section. The separate continuous-linear and
uniformly continuous completion problems retain their own scope.
