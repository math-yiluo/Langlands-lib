# Jointly continuous represented loci and their structural quotients

Author: Worker 56.

This internal construction uses the proved local and global spectrum
continuity theorems to lift the original represented-locus diagram and
its structural spectrum quotients to `ContAction TopCat H`.

Let `K : Type u` be a complete ultrametric normed field, let `P` be an
actual finite positive-polyradius presented affinoid quotient over `K`,
and let `G : Type v` be a topological group. The universes are independent.
Fix `ρ : DomainSpectralAction G P` and an open subgroup `H`. The input
continuity is into the existing represented-domain spectral topology;
joint spectrum continuity is a derived theorem.

For `d : ρ.InvariantDomain H`, `invariantLocusAction_isContinuous` proves
joint continuity of the existing restricted ambient action on
`d.obj.locus`. It composes `continuous_globalSpectrumAction` with the
continuous inclusion of `H × d.obj.locus` into `G × BanachSpectrum P`,
then restricts the codomain to the invariant locus. Both subgroup and
locus have their original subspace topologies. No quotient action or
replacement topology is chosen.

`invariantLocusFunctor` lifts the full existing invariant-locus functor
through the full subcategory of jointly continuous actions. It keeps
every actual bounded domain arrow's continuous locus inclusion. The
operator sends the underlying point `x` to `ρ(g) • x`, whose value at
`a : P` is `x ((ρ(g)).inv a)`. The object and arrow formulas and both
forgetting identities follow definitionally.

`invariantSpectrumToLocusContinuous` lifts exactly the existing equivariant
map `d.obj.spectrumToLocus`. It pulls a section seminorm back along the
actual bounded structural map and records membership in the represented
locus. Its source is the proved continuous invariant spectrum action;
its target is the continuous locus action just constructed. The full
subcategory retains the original equivariance equation.

The exposed surjectivity, closedness and quotient-map theorems are the
existing structural quotient results for this same map and the actual
locus subspace topology. They assert no injectivity. For each bounded
domain restriction, `invariantSpectrumToLocusContinuous_naturality`
retains the original commuting quotient square. These maps assemble as
`invariantSpectrumToLocusContinuousNatTrans`. Forgetting continuity gives
the preceding equivariant natural transformation; forgetting the actions
also gives the original topological structural natural transformation.

The provenance is internal: the proof restricts the established ambient
joint action and lifts the concrete constructions of
`DomainInvariantLocus` and `DomainSpectralContinuousAction` through
Mathlib's full subcategory. It requires no new literature assertion,
extra continuity premise or norm-continuous algebra orbits. Empty loci
and spectra, zero quotients, nilpotents and trivial scalar valuations
remain allowed. Analytic atlases, structure sheaves, comparison with all
compact analytic-domain tests, analytic etale sites and the Harris tower
specialization remain further work.
