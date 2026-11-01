# Subgroup compatibility of continuous represented-domain diagrams

Author: Worker 56.

Let `K : Type u` be a complete ultrametric normed field, `P` an actual
finite positive-polyradius presented affinoid quotient, and `G : Type v`
a topological group, with the two universes independent. Fix a
`DomainSpectralAction G P`, open subgroups `J` and `H`, and `h : J ≤ H`.
The continuity input is the existing represented-domain spectral test
topology. Joint continuity of the spectrum and locus actions has already
been derived in the imported local and global proofs.

This unit proves that the continuous diagrams commute with subgroup
restriction. The domain restriction functor retains every actual represented
domain and bounded restriction map, and weakens its preservation witness
from `H` to `J`. The group inclusion is the published
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.openSubgroupInclusion`.
Mathlib's `ContAction.res` restricts along this continuous inclusion and
retains the original topological spaces and action operators.

`invariantSpectrumFunctor_subgroup` and `invariantLocusFunctor_subgroup`
are equalities of the complete functors: first restricting invariant domains
and then forming the `J` diagram agrees with first forming the `H` diagram
and then restricting continuous actions. Thus every bounded spectrum
pullback and locus inclusion is retained, as well as each object's action.
`restrictedGlobalSpectrum_subgroup` identifies the two possible
restrictions of the original ambient continuous spectrum action.

The three component identities retain the actual bounded structural
spectrum pullback, actual locus inclusion, and actual surjective structural
spectrum-to-locus quotient. The theorem
`invariantSpectrumToLocusContinuousNatTrans_subgroup` identifies the entire
quotient natural transformations after the two restrictions. It includes
all naturality squares, rather than just the quotient at one domain.

`invariantSpectrumOverFunctor_subgroup` and
`invariantLocusOverFunctor_subgroup` give the corresponding equalities of
full overcategory diagrams. Their base is the same restricted original
continuous spectrum action by `restrictedGlobalSpectrum_subgroup`.
Finally, `invariantSpectrumToLocusOverNatTrans_subgroup` identifies the
whole quotient natural transformation in that overcategory. It retains
both each actual structural map to the base and each quotient component.

The definitions `invariantSpectrumOverSubgroupIso` and
`invariantLocusOverSubgroupIso` turn the two overcategory functor identities
into natural comparison isomorphisms via `eqToIso`. Their components are
identity maps on the unchanged objects. The theorem
`invariantSpectrumToLocusOverSubgroupIso_comm` proves that these comparisons
intertwine the full quotient natural transformations; its proof evaluates
the components of the natural transformations.

The preceding subgroup identities are proved by definitional equality. After unfolding the
existing constructions, the two subgroup paths apply the same original
group element and the same bounded maps. The preservation witnesses and
joint-continuity proofs are proposition-valued; they introduce no new
operator or topology. This is an internal consequence of
`DomainInvariantSubgroupRestriction`, `DomainEquivariantSubgroupRestriction`
and `DomainContinuousOverBase`, not a new external literature assertion.

Empty loci and spectra, nilpotents, zero quotients and trivial scalar
valuations remain permitted. The result constructs compatibility of existing
continuous geometric diagrams. Analytic structure sheaves, analytic atlases,
analytic etale sites, comparison with all compact analytic-domain tests
and the Harris specialization remain separate obligations.
