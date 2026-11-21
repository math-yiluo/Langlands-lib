# Independent one-sided translation recurrences in L²

`Langlands.Analysis.L2IndependentSlabsStatement`, proved by `l2IndependentSlabs`,
combines finitely many renormalizing shifts on one measure space. Each shift
increases its own real height by one and leaves all other listed heights
unchanged. The **positive region** is the intersection of the positive
half-spaces. The **boundary box** intersects the intervals `(0,mᵢ]` in the
respective height coordinates, where `mᵢ` is the degree of the monic
recurrence in direction `i`. The shift and measure hypotheses are those of
`L2RenormalizingShift`.

For all directions, assume the sufficient coefficient bound
`∑ₖ |pᵢₖ| cᵢᵏ < cᵢ^mᵢ`. Then there is a constant `C ≥ 1` depending on the
shifts, degrees and coefficients, not on `f` or its target normed space.
If a strongly measurable function `f` is square-integrable on the boundary
box and every difference residual `Dᵢ f` is square-integrable on the
positive region, then `f` is square-integrable on the positive region and

```
‖f‖_positive ≤ C (‖f‖_box + ∑ᵢ ‖Dᵢ f‖_positive).
```

No commutation of the point transformations is assumed beyond their
stated effects on the heights. The indexing may be any finite subset of
an index type, including the empty set.

## Implemented proof

`L2RenormalizingShift.restrict` restricts the measure to a measurable set
preserved under taking preimages by the shift. The pushforward scaling
survives by `Measure.restrict_map` and `Measure.restrict_smul`. The auxiliary
`lowerMass_lt_of_sum_lt` shows that a scale `c ≥ 1` strictly exceeding the sum
of the lower coefficient norms satisfies the weighted coefficient bound.

`L2IndependentSlabs.memLp_and_lpNorm_le` inducts on the finite set of
coordinates. For a new direction `i`, first restrict the measure to its
initial slab. All old shifts preserve this slab. The induction hypothesis
then supplies square-integrability and the bound on the intersection of
that slab with the old positive region. In this application the old boundary
box, intersected with the new slab, is the full boundary box. The old
residuals are restricted from the full positive region, so their norms do
not increase. Next restrict the original measure to the old positive
region, which the new shift preserves. Apply the single-direction theorem
to `i`; its required boundary norm has just been estimated. The equalities
between successive restrictions and intersections use
`Measure.restrict_restrict`.

For each direction, the single-direction norm estimate is bounded by
`K` times the sum of its boundary and residual norms, for any
`K ≥ (cᵢ^mᵢ + 1)/(cᵢ^mᵢ − ∑ₖ |pᵢₖ| cᵢᵏ)`. If one `K ≥ 1` works for all
directions and `R` bounds every input norm, the induction gives
`(2K)^card(t) R`. The final theorem chooses `K` as one plus the sum of the
absolute values of those majorants and `R` as the sum of the full input
norms. The square-integrability conclusion is established at both
restriction steps, not inferred from a finite bound on the realized
`lpNorm` alone.

## Provenance and scope

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.5 Corollary,
p.218, and its application in §7.5 Proposition, p.219, and §7.6,
pp.219–220. This derived variant implements the finite-direction induction
with the stronger sufficient coefficient bound from `L2SlabRecurrence`
and adds the membership conclusion used when lifting actual solutions.
It does not construct the relative adelic Siegel domains, the operators on
their Hilbert spaces, or the compact boundary terms.
