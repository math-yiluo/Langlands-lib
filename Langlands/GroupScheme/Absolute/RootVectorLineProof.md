# Actual absolute root subgroups are vector groups of dimension one: proof

`absoluteRootVectorLine` proves the unchanged published
`AbsoluteRootVectorLineStatement.{u}` from
`Langlands.GroupScheme.Absolute.RootVectorLineStatement`, at every universe
`u`. Its type is exactly that proposition. It has no hypotheses.

The statement concerns an algebraically closed field `k : Type u` of any
characteristic, a connected reductive group `G` over `k`, and a split
subtorus `t : T.toGrp ⟶ G` that is a maximal torus. For every `α` in
`relativeRoots t`, it gives an actual group scheme `U` and a closed immersion
`j : U ⟶ G`. The range of `j` represents the intrinsic all-test root functor
`RelativeRoot.subgroup t α`. The group `U` satisfies
`RelativeRoot.IsVectorGroupOfDimension U 1`, so it has natural additive
coordinates on every relative test scheme, including nonreduced ones.

## Implemented proof

The proof is a single application of the published reduction
`absoluteRootVectorLineStructuralReduction`. That theorem proves
`AbsoluteRootVectorLineStructuralReductionStatement.{u}`: the three
structural statements below, in this order, imply
`AbsoluteRootVectorLineStatement.{u}`. The proof supplies a published proof
of each statement:

1. `solvableProperFixedPoint : SolvableProperFixedPointStatement.{u}`, from
   `Langlands.GroupScheme.SolvableProperFixedPointProof`;
2. `solvableTorusQuotient : SolvableTorusQuotientStatement.{u}`, from
   `Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof`;
3. `dynamicCentralizerReductive : DynamicCentralizerReductiveStatement.{u}`,
   from `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`.

The reduction itself is in
`Langlands.GroupScheme.Absolute.RootVectorLineStructuralAssembly`. It
discharges `ProjectiveTorusFixedPointDimensionStatement` with the published
proof `projectiveTorusFixedPointDimension`. It derives maximal-torus
conjugacy in solvable groups from the torus-quotient input and the published
`unipotentSplitTorusDomination`. It derives maximal-torus centralizers over
algebraically closed fields from the dynamic-centralizer and torus-quotient
inputs. It then bounds the dimension of each intrinsic root tangent by one.
Using the dynamic-centralizer input, it reduces this bound to connected
reductive groups in which any two actual roots are integrally dependent.
There it applies `rankOne_rootTangent_le_one_of_projectiveBorelInputs` to
the fixed-point, projective-dimension, conjugacy and centralizer statements.
The published bridge `absoluteRootVectorLine_of_tangentBound` turns
this bound into the conclusion. It combines the published closed root
realization, the nonzero intrinsic root tangent, smooth relative dimension,
and the perfect-field classification of one-dimensional unipotent groups.
The paired Markdown of the assembly module describes these steps in detail.

No root reducedness, rank-one classification, pre-existing root realization,
primitive root character, smooth character kernel or dimension bound is
assumed. Root realization, vector-group coordinates and dimension one are all
conclusions.

## Provenance

The statement's source is J. S. Milne, *Algebraic Groups*, corrected 2022
reprint, Definition 21.10 and Theorem 21.11(b),(c), printed pp.428–429 /
PDF pp.439–440. Milne obtains the additive coordinates from a central-kernel
homomorphism from `SL₂`. The implemented route is different. It works
directly with the unchanged intrinsic orbit-extension root functor and
bounds its tangent through rank-one quotient curves and generic dynamic
centralizers. This module only composes published Library theorems and makes
no new literature claim. It changes neither the target statement nor any
imported file.
