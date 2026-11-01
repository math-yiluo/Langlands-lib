# Locally constant functions on compact represented affinoid domains

Worker 56 constructs open function stabilizers for the actual generalized
affinoid domains already implemented in the imported modules. For an open
subgroup `H` preserving a full represented domain `d`,
`invariantLocusFunctionStabilizer` is the subgroup of `H` satisfying
`f (invariantLocusOperator g x) = f x` for every point of the represented
locus. The function has an arbitrary coefficient set in an independent
universe.

Openness is derived from `Domain.compactSpace_locus` and the proved
`invariantLocusAction_isContinuous`. The generic compact-action helper
turns these into uniform fixedness near the identity. A stabilizer, a
smoothness witness, or a discrete topology on the analytic locus is not
assumed.

`invariantLocusFunctionPullback` is precomposition with the original
`spectrumToLocus`. `invariantSpectrumFunctionStabilizer` applies the same
construction directly to the actual compact representing spectrum, using
the previously proved local joint spectral continuity.
`invariantLocusFunctionPullback_stabilizer` proves equality of the entire
upstairs and downstairs open stabilizers. The forward implication uses
surjectivity of `spectrumToLocus`, and both implications use its original
equivariance equation. There is no injectivity assumption or replacement
of the represented locus by its representing spectrum.

`invariantLocusFiniteFunctionStabilizer` intersects the open stabilizers of
any finite family, with its exact pointwise membership criterion. Empty
loci and empty families are allowed. Positive polyradii, quotient
algebras with nilpotents and trivial absolute values remain as in the
imported domain implementation.

This is an internal consequence of the existing actual domain compactness
and action continuity constructions, providing compact-domain local action
data for later smooth-section work. Its mathematical provenance is precisely
those imported constructions and the compact-uniformity argument explained
in the helper's paired Markdown. It is not an assertion about all sections
of an analytic étale sheaf, nor a construction of a smooth representation,
an analytic site or cohomology. The broader Berkovich/Harris analytic
construction remains an independent obligation.
