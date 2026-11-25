# Intrinsic cuspidality along proper opposite radicals

This internal transport module supplies the convergence and vanishing needed
for the cuspidal cancellation step of the actual-point VIII.3.1 proof.
It derives this property from the defining intrinsic standard kernel and
existing group structure. It does not assume the full semistandard-kernel
comparison, constant-term estimates, or any recursive-image comparison.

`conjugationSubgroupContinuousMulEquiv` restricts ambient conjugation
`x ↦ g x g⁻¹` to two subgroups whose membership conditions correspond under
that conjugation. The subgroups have their induced topologies and Borel
measurable structures. Closedness is not needed for this equivalence.

`isIntegrableUnipotentCuspidal_of_conjugation` assumes that the all-translates
integral of a function along the first subgroup is integrable and zero for
every Haar measure on that subgroup. It proves the same property for any
Haar measure on the second subgroup. Pull back that Haar measure along
the inverse continuous group equivalence, which again yields a Haar
measure. The original kernel property applies at the translated arguments
`x g` and `g⁻¹ y`. Change of variables along the measurable equivalence
identifies both the integrability assertion and the integral with those on
the second subgroup. There is no measure normalization or scalar choice.

On actual rational points of a connected reductive group over any
nonarchimedean local field, fix a maximal split torus and generic
cocharacter. For every proper finite standard subset `I` and every
standard cocharacter `ζ` for it,
`isIntegrableUnipotentCuspidal_opposite_of_mem_rationalCuspidalSubmodule`
proves this all-translates property along the actual dynamic opposite
radical `oppositeUnipotent i ζ` for an intrinsic cuspidal Schwartz function.
The compact open Iwasawa subgroup and nonempty finite matrix realization
are those defining its Schwartz space; no relation between the compact
subgroup and the matrix height is imposed.

The proof obtains a finite actual relative-Weyl Coxeter system from
`relativeWeylCoxeter`, chooses a rational normalizer lift of the longest
representative for `I`, and uses
`standardAssociatedOppositeTransport.mem_rationalPoints` to identify its
conjugation from the associated standard radical onto the specified
opposite radical. The associated index has the same cardinality as `I`,
so it is proper whenever `I` is proper. The defining intrinsic kernel
therefore supplies the original all-translates property for every Haar
measure, and the generic transport applies.

The closed group-structure theorems, rather than their statement
definitions, discharge the Coxeter realization and opposite transport.
In relative rank zero there is no proper `I`, so the implication has no
proper-index instance. This module proves no decay estimate.
