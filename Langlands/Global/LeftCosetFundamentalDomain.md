# Borel fundamental domains for left cosets

This internal construction applies to an arbitrary subgroup `Γ` of a
second-countable topological group `H`, with the Borel measurable structure
on `H`. Its sole subgroup hypothesis is that `Γ` is discrete in the subspace
topology. It uses the actual left orbit quotient `LeftCosetSpace Γ = Γ \ H`.
It does not require normality, local compactness, or an invariant ambient
measure to construct its domain.

The quotient projection is a covering map by the pinned Mathlib discrete
subgroup theorem in `Topology/Covering/Quotient`. In particular it is
locally injective. The Lindelöf theorem gives a countable open cover
`U n` on which the projection is injective. The implemented domain is the
union, over `n`, of the points of `U n` whose quotient image belongs to none
of the earlier images `mk Γ '' U m`, for `m < n`. Those images are open,
so the domain is Borel. Every quotient fiber first meets one patch; the
least-index argument gives existence, and injectivity on that patch
gives uniqueness. The free left subgroup action converts uniqueness of
the representative to uniqueness of the element of `Γ` carrying a given
point to the domain.

`exists_measurable_fundamentalDomain` proves this exact, everywhere
uniqueness property. `fundamentalDomain` chooses such a Borel set
independently of a measure. `isFundamentalDomain` proves that it is a
Mathlib fundamental domain for **every** measure on `H`. The
`hasFundamentalDomain` theorem provides the corresponding typeclass value.
No invariance is needed for these assertions, since the translates form
an exact partition, stronger than an almost-everywhere partition.

`countable_of_isDiscrete` derives countability of `Γ` from second
countability of `H`: its discrete subspace is second countable and hence
separable, and a separable discrete space is countable. Thus countability
is not an additional input to the remaining exports.

`discreteQuotientMeasure` is the pushforward of the ambient measure
restricted to the chosen Borel domain. Under invariance by `Γ`, it agrees
with the measure from every other supplied fundamental domain and has
the quotient preimage compatibility property of `LeftCosetMeasure`.
For a two-sided invariant ambient measure, every positive right
translation of the quotient preserves it. These conclusions reuse the
domain-independence and translation proofs in `LeftCosetMeasure`; they
do not assume that the subgroup is normal.

The construction is derived from the cited pinned Mathlib covering,
Lindelöf, discrete-space and fundamental-domain APIs and the explicit
first-patch argument above, without an original-literature identification.
It supplies a generic domain-existence prerequisite. Actual rational
adelic subgroup discreteness, the ambient group topology and Haar
measure, reductive unimodularity, finite covolume, reduction theory and
the split-centre comparison remain separate obligations.
