# Finiteness transport to smooth infinite slices

Author: Worker 94. The theorem
`Langlands.Automorphic.SliceFinitenessProof.sliceFiniteness` proves the published
`Langlands.Automorphic.SliceFinitenessStatement K n`, for arbitrary
`K : Type u`, `[Field K]`, `[NumberField K]`, and `n : ℕ`, including rank zero.
It imports the unchanged statement module and its existing concrete actions.

The proof is an internal algebraic consequence of the published finite-vector
transport lemmas, with no additional theorem from the literature.
`centerEvaluation` is evaluation of a family at a finite adelic argument as
a complex linear intertwiner. Its equivariance is definitional: the center
acts on each coordinate by the same actual center differential operator.
`centerFiniteFamilyEvaluation` applies
`Langlands.FiniteVectors.IsFiniteVector.map` to this intertwiner.
The simultaneous center-finite hypothesis on the entire family is retained.

For subgroup finiteness, `smoothSubgroupAction` restricts actual smooth
adelic right translation along the infinite subgroup inclusion.
`smoothSubgroupInclusion` is the injective smooth-to-continuous inclusion
for these restricted actions. The proof uses
`Langlands.FiniteVectors.isFiniteVector_map_iff` and subtype injectivity to
reflect the assumed finite orbit from the continuous carrier to the smooth
carrier.
For typeclass elaboration the proof locally obtains the smooth carrier's
additive-group structure from its existing complex module using
`Module.addCommMonoidToAddCommGroup`; it adds no mathematical hypothesis.

`smoothSliceIntertwiner` is the existing `smoothInfiniteSlice` linear map,
now bundled with its equivariance for the subgroup actions. Evaluating at
an infinite matrix reduces equivariance to
`pair(a,b) * ofInfinite(k) = pair(a*k,b)`, proved by
`AdelicGL.ofInfinite_eq_pair`, `AdelicGL.pair_mul`, and multiplication by
one. Applying finite-vector image preservation to this map proves
`smoothSliceSubgroupFinite`. The final theorem pairs these two implications.

No compactness, common finite level, or growth hypothesis is needed for the
subgroup implication. The proof preserves every infinite-factor subgroup and
every finite adelic slice. It proves neither the converse to center-family
evaluation nor compact-group-to-differential finiteness, joint finiteness,
reproducing kernels, or the final derivative-growth theorem.
