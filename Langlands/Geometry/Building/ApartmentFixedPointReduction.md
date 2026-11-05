# From an apartment fixed locus to a global fixed point

This internal deduction concerns one supplied `ValuationBuildingData G`, its
existing `ReducedBuilding`, its existing action by the actual `rationalPoints G`,
and its existing translated-apartment subsets. It constructs no building datum,
metric, canonical integral model or comparison.

`HasCommonApartmentWith x` is a proposition saying that every point of the
existing quotient shares a translated apartment with `x`.
`HasApartmentFixedPointUniqueness K x` is a proposition saying that every
`K`-fixed point in the base apartment equals `x`. The latter asserts uniqueness
only; it does not assert that `x` is fixed or even lies in the base apartment.
These internal predicates name the two retained geometric obligations in the
reduction below and do not postulate their truth.

`mem_apartmentImage_of_fixed` assumes that every point shares an apartment with
a specified point `x`, and that a specified subgroup `K` moves every apartment
through `x` to the base apartment. Given a point `y` fixed by every element of
`K`, choose a common apartment `Y` and an element `g` of `K` carrying `Y` to
the base apartment. Then `g • y` belongs to the base apartment and equals `y`.

`eq_of_fixed_of_apartment` combines that conclusion with an explicit singleton
fixed-locus calculation inside the base apartment. Thus it extends apartment
uniqueness to global uniqueness for the same original subgroup `K`.

`exists_sharpFixer_smul_apartmentImage` proves the required transitivity for
the actual sharp fixer at any base-apartment point. If `apartmentMap x` lies
in `g • apartmentImage`, write it as `g • apartmentMap z`. Equality of these
two quotient representatives gives a normalizer element `n` with
`g * n ∈ sharpFixer {x}`. Since the normalizer preserves the base apartment,
the inverse of `g * n` carries the given apartment to the base apartment.
This uses the existing quotient relation and its existing sharp-fixer family;
it requires neither apartment injectivity nor a separate transitivity axiom.

`eq_of_fixed_of_sharpFixer_le` applies this construction to every subgroup
containing that sharp fixer. The final
`eq_of_compactStabilizer_fixed_of_apartment` specializes it to the existing
norm-one point stabilizer, using the published inclusion of the sharp fixer
in that stabilizer under `IsTopologyCompatible`. This is exactly the
existing compact stabilizer, rather than the full point fixer.

The deduction is elementary group-action reasoning. Its intended application
is the separation between the apartment fixed-locus calculation and the
global fixed-point requirement for a supplied integral model. Common-apartment
coverage and the apartment fixed-locus calculation remain explicit hypotheses
of the final helper. Identifying the stabilizer with the supplied integral-model
image is a separate obligation, as is constructing topology-compatible valuation
data in the first place. The first two general-subgroup helpers retain their
explicit transitivity premise, which the later quotient construction discharges
for the specified subgroups. No general existence or reductive-group comparison
theorem is inferred from these deductions.
No residue-cardinality restriction is used in the implemented deduction.
