# Discrete continuous function actions on actual represented domains

Worker 56 constructs continuous actions on the discrete spaces of locally
constant functions on an invariant represented locus and on its original
representing spectrum. The inputs are an actual `PresentedAffinoidAlgebra`
`P` over a complete ultrametric normed field, its `DomainSpectralAction`
of a topological group `G`, an open subgroup `H`, an `H`-invariant actual
represented domain `d`, and an arbitrary coefficient set `A` in an
independent universe.

`invariantLocusLocallyConstantAction` uses the original restricted ambient
locus action. Its operator is
`(g • f)(x) = f(invariantLocusOperator H d g⁻¹ x)`.
`invariantSpectrumLocallyConstantAction` uses the original inverse-pullback
action on the entire representing spectrum. Its function operator is
`(g • f)(x) = f((invariantSectionAction H d g⁻¹) • x)`.
Both are objects of `ContAction TopCat H`. The function carriers are the
`DiscreteLocallyConstant` wrappers of exactly those locally constant
function sets, with the discrete topology. The open subgroup retains its
original subspace topology, and `A` has no topology or action.

The constructed continuous actions follow from the published joint
continuity of the actual locus and spectrum actions and compactness of
those actual spaces. The generic companion proves that stabilizers for
inverse precomposition equal the existing full function stabilizers.
Their proved openness and Mathlib's discrete-action continuity criterion
then supply joint continuity. No supplied function-fixedness condition
or replacement topology on the geometric spaces is used.

`invariantLocallyConstantActionPullback` is a continuous equivariant
morphism between these two function actions. It uses the exact original
`spectrumToLocus` map: its value at `x` is `f(spectrumToLocus x)`.
The original structural equivariance equation at `g⁻¹` proves the
function-action equivariance equation. Its injectivity follows by
evaluating functions at a preimage under the already proved surjective
structural map. This does not identify the spectrum with the locus or
claim every spectrum function descends.

This is an internal construction from the actual compact represented
domain actions, the existing structural quotient and the generic
continuous function-action construction. It retains positive polyradii,
quotients by arbitrary closed ideals, nilpotents, trivially valued fields
and empty loci or spectra. It supplies constant-coefficient compact local
function data. Arbitrary equivariant sheaf sections, analytic site
comparison, and Harris tower constructions remain separate obligations.
